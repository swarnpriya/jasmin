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

(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import seq tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import JMeq ZArith Setoid Morphisms.

Require Import word dmasm_utils dmasm_type dmasm_var dmasm_expr.
Require Import memory dmasm_sem dmasm_Ssem dmasm_Ssem_props.
(*Require Import symbolic_expr symbolic_expr_opt.*)

Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive mexpr : Type :=
    Mvar : var -> mexpr
  | Mconst : Z -> mexpr
  | Mbool : bool -> mexpr
  | Madd : mexpr -> mexpr -> mexpr
  | Mand : mexpr -> mexpr -> mexpr.

Variant minstr : Type :=
  MCassgn : var -> mexpr -> minstr.

Notation mcmd := (seq minstr).

Fixpoint msem_mexpr (s: svmap) (e: mexpr) : exec svalue :=
  match e with
  | Mvar v => ok (sget_var s v)
  | Mbool b => ok (SVbool b)
  | Mconst z => ok (SVint z)
  | Madd e1 e2 =>
    Let x1 := msem_mexpr s e1 in
    Let x2 := msem_mexpr s e2 in
    Let i1 := sto_int x1 in
    Let i2 := sto_int x2 in
    ok (SVint (i1 + i2))
  | Mand e1 e2 =>
    Let x1 := msem_mexpr s e1 in
    Let x2 := msem_mexpr s e2 in
    Let i1 := sto_bool x1 in
    Let i2 := sto_bool x2 in
    ok (SVbool (andb i1 i2))
  end.

Fixpoint trace_expr (s: svmap) (e: mexpr) :=
  match e with
  | Mvar v => [:: sget_var s v]
  | Mbool b => [::]
  | Mconst z => [::]
  | Madd e1 e2 => (trace_expr s e1) ++ (trace_expr s e2)
  | Mand e1 e2 => trace_expr s e1
  end.

Definition trace_instr (s: svmap) (c: minstr) :=
  match c with
  | MCassgn _ e => trace_expr s e
  end.

Print write_rval.

Inductive msem : svmap -> mcmd -> svmap -> Prop :=
    MEskip : forall s : svmap, msem s [::] s
  | MEseq : forall (s1 s2 s3 : svmap) (i : minstr) (c : mcmd),
           msem_I s1 i s2 -> msem s2 c s3 -> msem s1 (i :: c) s3
  with msem_I : svmap -> minstr -> svmap -> Prop :=
  | MEassgn : forall (s1 s2 : svmap) (x : var) (e : mexpr),
    Let v := msem_mexpr s1 e in sset_var s1 x v = ok s2 ->
    msem_I s1 (MCassgn x e) s2.

Fixpoint foo_I (s: svmap) (c: minstr) (s': svmap) :=
  match c with
  | MCassgn v e => [:: v]
  end.

Fixpoint foo (s: svmap) (c: mcmd) (s': svmap) (p: msem s c s') {struct p} :=
  match c with
  | [::] => [::]
  | i :: c =>
    (match p with
    | MEskip _ => _
    | MEseq _ s1 _ _ _ _ H => (foo_I s i s1) ++ (foo _(*s1 c s'*))
    end)
  end.

Lemma msem_inv s c s' :
  msem s c s' →
  match c with
  | [::] => s' = s
  | i :: c' => ∃ s1, msem_I s i s1 ∧ msem s1 c' s'
end.
Proof. by case; eauto. Qed.

Lemma msem_I_inv s i s' :
  msem_I s i s' →
  match i with
  | MCassgn x e => ∃ v, msem_mexpr s e = ok v ∧ sset_var s x v = ok s'
  end.
Proof.
  by case=> s1 s2 x e H; case: (bindW H); eauto.
Qed.
