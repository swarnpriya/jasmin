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

Definition lprod ts tr :=
  foldr (fun t tr => t -> tr) tr ts.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.

Fixpoint ltuple (ts:list Type) : Type := 
  match ts with
  | [::]   => unit 
  | [::t1] => t1
  | t1::ts => t1 * ltuple ts
  end.

Notation "(:: x , .. , y & z )" := (pair x .. (pair y z) ..).

Definition toto : ltuple [:: (nat:Type); (nat:Type); (nat:Type); (nat:Type)] := 
  (:: 0, 0, 0 & 0).

Fixpoint merge_tuple (l1 l2: list Type) : ltuple l1 -> ltuple l2 -> ltuple (l1 ++ l2) := 
  match l1 return ltuple l1 -> ltuple l2 -> ltuple (l1 ++ l2) with 
  | [::] => fun _ p => p
  | t1 :: l1 => 
    let rec := @merge_tuple l1 l2 in 
    match l1 return (ltuple l1 -> ltuple l2 -> ltuple (l1 ++ l2)) -> 
                    ltuple (t1::l1) -> ltuple l2 -> ltuple (t1 :: l1 ++ l2) with
    | [::] => fun _ (x:t1) =>
      match l2 return ltuple l2 -> ltuple (t1::l2) with
      | [::] => fun _ => x
      | t2::l2    => fun (p:ltuple (t2::l2)) => (x, p)
      end
    | t1' :: l1' => fun rec (x:t1 * ltuple (t1'::l1')) p =>
      (x.1, rec x.2 p)
    end rec
   end.
   
Definition titi : ltuple [:: (nat:Type); (nat:Type); (nat:Type); (nat:Type); (nat:Type); (nat:Type); (nat:Type); (nat:Type)]:= merge_tuple toto toto.

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
  tin_narr : all is_not_sarr tin
}.

(* ----------------------------------------------------------------------------- *)
Definition pp_s     (s: string)                         (_: unit) : string := s.
Definition pp_sz    (s: string) (sz: wsize)             (_: unit) : string := s ++ " " ++ string_of_wsize sz.
Definition pp_sz_sz (s: string) (sz sz': wsize)         (_: unit) : string := s ++ " " ++ string_of_wsize sz ++ " " ++ string_of_wsize sz'.
Definition pp_ve_sz (s: string) (ve: velem) (sz: wsize) (_: unit) : string := s ++ " " ++ string_of_velem ve ++ " " ++ string_of_wsize sz.
Definition pp_ve    (s: string) (ve: velem)             (_: unit)   : string := s ++ " " ++ string_of_velem ve.

(* ----------------------------------------------------------------------------- *)
Definition b_ty             := [:: sbool].
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

Notation mk_instr str tin tout semi :=
  {| str := str; tin := tin; tout := tout; semi := semi; tin_narr := refl_equal |}.

Definition mk_instr_w2_w2 name semi sz :=
  mk_instr (pp_sz name sz) (w2_ty sz sz) (w2_ty sz sz) (semi sz).

Definition mk_instr_w2b_bw name semi sz :=
  mk_instr (pp_sz name sz) [::sword sz; sword sz; sbool] (sbool :: (w_ty sz)) 
   (fun x y c => let p := semi sz x y c in ok (Some p.1, p.2)).

Definition mk_instr__b5w name semi sz :=
  mk_instr (pp_sz name sz) [::] (b5w_ty sz) (semi sz).

Definition mk_instr_w name semi sz :=
  mk_instr (pp_sz name sz) (w_ty sz) (w_ty sz) (semi sz).

Definition mk_instr_w2_b5w name semi sz :=
  mk_instr (pp_sz name sz) (w2_ty sz sz) (b5w_ty sz) (semi sz).

(* ----------------------------------------------------------------------------- *)
