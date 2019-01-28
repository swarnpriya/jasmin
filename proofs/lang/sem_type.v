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

(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq.
Require Export strings warray.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition sem_t (t : stype) : Type :=
  match t with
  | sbool    => bool
  | sint     => Z
  | sarr n   => WArray.array n
  | sword s  => word s
  end.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.

(* Definition example : ltuple [:: (nat:Type); (nat:Type); (nat:Type); (nat:Type); (nat:Type); (nat:Type); (nat:Type); (nat:Type)]:= merge_tuple toto toto.
 *)
Definition sem_ot (t:stype) : Type :=
  if t is sbool then option bool
  else sem_t t.

Definition sem_tuple ts := ltuple (map sem_ot ts).

(* ----------------------------------------------------------------------------- *)

Definition is_not_sarr t := ~~ is_sarr t.

Record Instruction := mkInstruction {
  str  : unit -> string;
  tin  : list stype;
  tout : list stype;
  semi : sem_prod tin (exec (sem_tuple tout));
  tin_narr : all is_not_sarr tin;
  wsizei : wsize;
}.

(*
The field wsizei ....
*)
(*
Definition wsize_of_sopn (op: sopn) : wsize :=
  match op with
  | Ox86_SETcc => U8
  | Omulu x
  | Oaddcarry x
  | Osubcarry x
  | Oset0 x
  | Ox86_MOV x
  | Ox86_MOVSX _ x
  | Ox86_MOVZX _ x
  | Ox86_CMOVcc x
  | Ox86_ADD x
  | Ox86_SUB x
  | Ox86_MUL x
  | Ox86_IMUL x
  | Ox86_IMULt x
  | Ox86_IMULtimm x
  | Ox86_DIV x
  | Ox86_IDIV x
  | Ox86_CQO x
  | Ox86_ADC x
  | Ox86_SBB x
  | Ox86_NEG x
  | Ox86_INC x
  | Ox86_DEC x
  | Ox86_BT x
  | Ox86_LEA x
  | Ox86_TEST x
  | Ox86_CMP x
  | Ox86_AND x
  | Ox86_ANDN x
  | Ox86_OR x
  | Ox86_XOR x
  | Ox86_NOT x
  | Ox86_ROR x
  | Ox86_ROL x
  | Ox86_SHL x
  | Ox86_SHR x
  | Ox86_SAR x
  | Ox86_SHLD x
  | Ox86_SHRD x
  | Ox86_BSWAP x
  | Ox86_VMOVDQU x
  | Ox86_VPAND x | Ox86_VPANDN x | Ox86_VPOR x | Ox86_VPXOR x
  | Ox86_VPADD _ x | Ox86_VPSUB _ x | Ox86_VPMULL _ x | Ox86_VPMULU x
  | Ox86_VPSLL _ x | Ox86_VPSRL _ x | Ox86_VPSRA _ x
  | Ox86_VPSLLV _ x | Ox86_VPSRLV _ x
  | Ox86_VPSLLDQ x | Ox86_VPSRLDQ x
  | Ox86_VPSHUFB x | Ox86_VPSHUFHW x | Ox86_VPSHUFLW x | Ox86_VPSHUFD x
  | Ox86_VPUNPCKH _ x | Ox86_VPUNPCKL _ x
  | Ox86_VPBLENDD x | Ox86_VPBROADCAST _ x
    => x
  | Ox86_MOVZX32 => U32
  | Ox86_MOVD _
  | Ox86_VPEXTR _ | Ox86_VPINSR _
    => U128
  | Ox86_VBROADCASTI128
  | Ox86_VEXTRACTI128
  | Ox86_VINSERTI128
  | Ox86_VPERM2I128
  | Ox86_VPERMQ
    => U256
  end.
*)
(* ----------------------------------------------------------------------------- *)
Definition pp_s     (s: string)                         (_: unit) : string := s.
Definition pp_sz    (s: string) (sz: wsize)             (_: unit) : string := s ++ " " ++ string_of_wsize sz.
Definition pp_sz_sz (s: string) (sz sz': wsize)         (_: unit) : string := s ++ " " ++ string_of_wsize sz ++ " " ++ string_of_wsize sz'.
Definition pp_ve_sz (s: string) (ve: velem) (sz: wsize) (_: unit) : string := s ++ " " ++ string_of_velem ve ++ " " ++ string_of_wsize sz.
Definition pp_ve    (s: string) (ve: velem)             (_: unit)   : string := s ++ " " ++ string_of_velem ve.

(* ----------------------------------------------------------------------------- *)
Definition b_ty             := [:: sbool].
Definition b4_ty            := [:: sbool; sbool; sbool; sbool].
Definition b5_ty            := [:: sbool; sbool; sbool; sbool; sbool].

Definition bw_ty    sz      := [:: sbool; sword sz].
Definition bw2_ty   sz      := [:: sbool; sword sz; sword sz].
Definition b2w_ty   sz      := [:: sbool; sbool; sword sz].
Definition b4w_ty   sz      := [:: sbool; sbool; sbool; sbool; sword sz].
Definition b5w_ty   sz      := [:: sbool; sbool; sbool; sbool; sbool; sword sz].
Definition b5w2_ty  sz      := [:: sbool; sbool; sbool; sbool; sbool; sword sz; sword sz].

Definition w_ty     sz      := [:: sword sz].
Definition w2_ty    sz sz'  := [:: sword sz; sword sz'].
Definition w3_ty    sz      := [:: sword sz; sword sz; sword sz].
Definition w4_ty    sz      := [:: sword sz; sword sz; sword sz; sword sz].
Definition w8_ty            := [:: sword8].
Definition w32_ty           := [:: sword32].
Definition w64_ty           := [:: sword64].
Definition w128_ty          := [:: sword128].
Definition w256_ty          := [:: sword256].

Definition w2b_ty   sz sz'  := [:: sword sz; sword sz'; sbool].
Definition ww8_ty   sz      := [:: sword sz; sword8].
Definition w2w8_ty   sz     := [:: sword sz; sword sz; sword8].
Definition w128w8_ty        := [:: sword128; sword8].
Definition w128ww8_ty sz    := [:: sword128; sword sz; sword8].
Definition w256w8_ty        := [:: sword256; sword8].
Definition w256w128w8_ty    := [:: sword256; sword128; sword8].
Definition w256x2w8_ty      := [:: sword256; sword256; sword8].

(* ----------------------------------------------------------------------------- *)

Notation mk_instr str tin tout semi wsizei:=
  {| str := str;
     tin := tin;
     tout := tout;
     semi := semi;
     tin_narr := refl_equal;
     wsizei := wsizei;
  |}.


Definition mk_instr_w2_w2 name semi sz :=
  mk_instr (pp_sz name sz) (w2_ty sz sz) (w2_ty sz sz) (semi sz) sz.

Definition mk_instr_w2b_bw name semi sz :=
  mk_instr (pp_sz name sz) [::sword sz; sword sz; sbool] (sbool :: (w_ty sz))
   (fun x y c => let p := semi sz x y c in ok (Some p.1, p.2)) sz.

Definition mk_instr__b5w name semi sz :=
  mk_instr (pp_sz name sz) [::] (b5w_ty sz) (semi sz) sz.

Definition mk_instr_b_w name semi sz :=
  mk_instr (pp_sz name sz) (b_ty) (w_ty sz) (semi sz) sz.



(* ----------------------------------------------------------------------------- *)
