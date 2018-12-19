(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)


(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require oseq.
Require Import ZArith
(* utils *)
strings
(* low_memory *)
(* word *)
sem_type
global
oseq
Utf8
Relation_Operators.
Import Memory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ==================================================================== *)
Definition label := positive.

(* -------------------------------------------------------------------- *)
Variant register : Type :=
  | RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

(* -------------------------------------------------------------------- *)
Variant xmm_register : Type :=
  | XMM0 | XMM1 | XMM2 | XMM3
  | XMM4 | XMM5 | XMM6 | XMM7
  | XMM8 | XMM9 | XMM10 | XMM11
  | XMM12 | XMM13 | XMM14 | XMM15
.

(* -------------------------------------------------------------------- *)
Variant rflag : Type := CF | PF | ZF | SF | OF | DF.

(* -------------------------------------------------------------------- *)
Variant scale : Type := Scale1 | Scale2 | Scale4 | Scale8.

(* -------------------------------------------------------------------- *)
Coercion word_of_scale (s : scale) : pointer :=
  wrepr Uptr match s with
  | Scale1 => 1
  | Scale2 => 2
  | Scale4 => 4
  | Scale8 => 8
  end.

(* -------------------------------------------------------------------- *)
(* disp + base + scale × offset *)
Record address : Type := mkAddress {
  ad_disp   : pointer;
  ad_base   : option register;
  ad_scale  : scale;
  ad_offset : option register;
}.

(* -------------------------------------------------------------------- *)
Variant condt : Type :=
| O_ct                  (* overflow *)
| NO_ct                 (* not overflow *)
| B_ct                  (* below, not above or equal *)
| NB_ct                 (* not below, above or equal *)
| E_ct                  (* equal, zero *)
| NE_ct                 (* not equal, not zero *)
| BE_ct                 (* below or equal, not above *)
| NBE_ct                (* not below or equal, above *)
| S_ct                  (* sign *)
| NS_ct                 (* not sign *)
| P_ct                  (* parity, parity even *)
| NP_ct                 (* not parity, parity odd *)
| L_ct                  (* less than, not greater than or equal to *)
| NL_ct                 (* not less than, greater than or equal to *)
| LE_ct                 (* less than or equal to, not greater than *)
| NLE_ct                (* not less than or equal to, greater than *).

Definition string_of_condt (c: condt) : string :=
  match c with
  | O_ct => "O"
  | NO_ct => "NO"
  | B_ct => "B"
  | NB_ct => "NB"
  | E_ct => "E"
  | NE_ct => "NE"
  | BE_ct => "BE"
  | NBE_ct => "NBE"
  | S_ct => "S"
  | NS_ct => "NS"
  | P_ct => "P"
  | NP_ct => "NP"
  | L_ct => "L"
  | NL_ct => "NL"
  | LE_ct => "LE"
  | NLE_ct => "NLE"
  end.

(* -------------------------------------------------------------------- *)


Scheme Equality for register.
Scheme Equality for xmm_register.
Scheme Equality for rflag.
Scheme Equality for scale.
Scheme Equality for condt.

Definition reg_eqMixin := comparableClass register_eq_dec.
Canonical reg_eqType := EqType register reg_eqMixin.

Definition xreg_eqMixin := comparableClass xmm_register_eq_dec.
Canonical xreg_eqType := EqType _ xreg_eqMixin.

Definition rflag_eqMixin := comparableClass rflag_eq_dec.
Canonical rflag_eqType := EqType rflag rflag_eqMixin.

Definition scale_eqMixin := comparableClass scale_eq_dec.
Canonical scale_eqType := EqType scale scale_eqMixin.

Definition address_beq (addr1: address) addr2 :=
  match addr1, addr2 with
  | mkAddress d1 b1 s1 o1, mkAddress d2 b2 s2 o2 =>
    [&& d1 == d2, b1 == b2, s1 == s2 & o1 == o2]
  end.

Lemma address_eq_axiom : Equality.axiom address_beq.
Proof.
case=> [d1 b1 s1 o1] [d2 b2 s2 o2]; apply: (iffP idP) => /=.
+ by case/and4P ; do 4! move/eqP=> ->.
by case; do 4! move=> ->; rewrite !eqxx.
Qed.

Definition address_eqMixin := Equality.Mixin address_eq_axiom.
Canonical address_eqType := EqType address address_eqMixin.

Definition condt_eqMixin := comparableClass condt_eq_dec.
Canonical condt_eqType := EqType condt condt_eqMixin.

(* -------------------------------------------------------------------- *)
Definition registers :=
  [:: RAX; RCX; RDX; RBX; RSP; RBP; RSI; RDI ;
      R8 ; R9 ; R10; R11; R12; R13; R14; R15 ].

Lemma registers_fin_axiom : Finite.axiom registers.
Proof. by case. Qed.

Definition reg_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK registers_fin_axiom).
Canonical reg_choiceType :=
  Eval hnf in ChoiceType register reg_choiceMixin.

Definition reg_countMixin :=
  PcanCountMixin (FinIsCount.pickleK registers_fin_axiom).
Canonical reg_countType :=
  Eval hnf in CountType register reg_countMixin.

Definition reg_finMixin :=
  FinMixin registers_fin_axiom.
Canonical reg_finType :=
  Eval hnf in FinType register reg_finMixin.

(* -------------------------------------------------------------------- *)
Definition xmm_registers :=
  [:: XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7; XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15 ].

Lemma xmm_registers_fin_axiom : Finite.axiom xmm_registers.
Proof. by case. Qed.

Definition xreg_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK xmm_registers_fin_axiom).
Canonical xreg_choiceType :=
  Eval hnf in ChoiceType xmm_register xreg_choiceMixin.

Definition xreg_countMixin :=
  PcanCountMixin (FinIsCount.pickleK xmm_registers_fin_axiom).
Canonical xreg_countType :=
  Eval hnf in CountType xmm_register xreg_countMixin.

Definition xreg_finMixin :=
  FinMixin xmm_registers_fin_axiom.
Canonical xreg_finType :=
  Eval hnf in FinType xmm_register xreg_finMixin.

(* -------------------------------------------------------------------- *)
Definition rflags := [:: CF; PF; ZF; SF; OF; DF].

Lemma rflags_fin_axiom : Finite.axiom rflags.
Proof. by case. Qed.

Definition rflag_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK rflags_fin_axiom).
Canonical rflag_choiceType :=
  Eval hnf in ChoiceType rflag rflag_choiceMixin.

Definition rflag_countMixin :=
  PcanCountMixin (FinIsCount.pickleK rflags_fin_axiom).
Canonical rflag_countType :=
  Eval hnf in CountType rflag rflag_countMixin.

Definition rflag_finMixin :=
  FinMixin rflags_fin_axiom.
Canonical rflag_finType :=
  Eval hnf in FinType rflag rflag_finMixin.

(* -------------------------------------------------------------------- *)
Module RegMap.
  Definition map := {ffun register -> u64}.

  Definition set (m : map) (x : register) (y : u64) : map :=
    [ffun z => if (z == x) then y else m z].
End RegMap.

(* -------------------------------------------------------------------- *)
Module XRegMap.
  Definition map := {ffun xmm_register -> u256 }.

  Definition set (m : map) (x : xmm_register) (y : u256) : map :=
    [ffun z => if (z == x) then y else m z].
End XRegMap.

(* -------------------------------------------------------------------- *)
Module RflagMap.
  Variant rflagv := Def of bool | Undef.

  Definition map := {ffun rflag -> rflagv}.

  Definition set (m : map) (x : rflag) (y : bool) : map :=
    [ffun z => if (z == x) then Def y else m z].

  Definition oset (m : map) (x : rflag) (y : rflagv) : map :=
    [ffun z => if (z == x) then y else m z].

  Definition update (m : map) (f : rflag -> option rflagv) : map :=
    [ffun rf => odflt (m rf) (f rf)].
End RflagMap.

(* -------------------------------------------------------------------- *)
Notation regmap   := RegMap.map.
Notation xregmap  := XRegMap.map.
Notation rflagmap := RflagMap.map.
Notation Def      := RflagMap.Def.
Notation Undef    := RflagMap.Undef.

Definition regmap0   : regmap   := [ffun x => 0%R].
Definition rflagmap0 : rflagmap := [ffun x => Undef].

Scheme Equality for RflagMap.rflagv.

Definition rflagv_eqMixin := comparableClass rflagv_eq_dec.
Canonical rflagv_eqType := EqType _ rflagv_eqMixin.

(* -------------------------------------------------------------------- *)
