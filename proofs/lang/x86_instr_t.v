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

(* ** Imports and settings *)
Require Import oseq.
Require Export ZArith Setoid Morphisms.
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Export strings sem_type.
Require Import xseq.
Import Utf8 ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

Variant x86_instr_t : Set :=
| Ox86_MOV     of wsize  (* copy *)
| Ox86_MOVSX of wsize & wsize (* sign-extension *)
| Ox86_MOVZX of wsize & wsize (* zero-extension *)
| Ox86_MOVZX32  (* Pseudo instruction for 32-bit to 64-bit zero-extension *)
| Ox86_CMOVcc  of wsize  (* conditional copy *)
| Ox86_ADD     of wsize  (* add unsigned / signed *)
| Ox86_SUB     of wsize  (* sub unsigned / signed *)
| Ox86_MUL     of wsize  (* mul unsigned *)
| Ox86_IMUL    of wsize  (* excat multiplication *)
| Ox86_IMULt   of wsize  (* truncated multiplication *)
| Ox86_IMULtimm of wsize (* truncated multiplication by an immediate value *)
| Ox86_DIV     of wsize  (* div unsigned *)
| Ox86_IDIV    of wsize  (* div   signed *)
| Ox86_CQO     of wsize  (* return 0 if the highest bit is 0 or -1 otherwise *)
| Ox86_ADC     of wsize  (* add with carry *)
| Ox86_SBB     of wsize  (* sub with borrow *)
| Ox86_NEG     of wsize  (* negation *)
| Ox86_INC     of wsize  (* increment *)
| Ox86_DEC     of wsize  (* decrement *)
| Ox86_SETcc             (* Set byte on condition *)
| Ox86_BT      of wsize  (* Bit test, sets CF *)
| Ox86_LEA     of wsize  (* Load Effective Address *)
| Ox86_TEST    of wsize  (* Bit-wise logical and CMP *)
| Ox86_CMP     of wsize  (* Signed sub CMP *)
| Ox86_AND     of wsize  (* bit-wise and *)
| Ox86_ANDN    of wsize  (* bit-wise and *)
| Ox86_OR      of wsize  (* bit-wise or  *)
| Ox86_XOR     of wsize  (* bit-wise xor *)
| Ox86_NOT     of wsize  (* bit-wise not *)
| Ox86_ROR     of wsize  (* right rotation *)
| Ox86_ROL     of wsize  (* left rotation *)
| Ox86_SHL     of wsize  (* unsigned / left  *)
| Ox86_SHR     of wsize  (* unsigned / right *)
| Ox86_SAR     of wsize  (*   signed / right *)
| Ox86_SHLD    of wsize  (* unsigned double-word / left  *)
| Ox86_SHRD    of wsize  (* unsigned double-word / right  *)

| Ox86_BSWAP of wsize (* byte swap *)

| Ox86_MOVD of wsize (* zero-extend to 128 bits *)
| Ox86_VMOVDQU of wsize (* 128/256-bit copy *)
| Ox86_VPAND of wsize (* 128/256-bit AND *)
| Ox86_VPANDN of wsize (* 128/256-bit AND-NOT *)
| Ox86_VPOR of wsize (* 128/256-bit OR *)
| Ox86_VPXOR of wsize (* 128/256-bit XOR *)

| Ox86_VPADD of velem & wsize (* Parallel addition over 128/256-bit vectors *)
| Ox86_VPSUB of velem & wsize (* Parallel addition over 128/256-bit vectors *)
| Ox86_VPMULL of velem & wsize (* Parallel addition over 128/256-bit vectors *)
| Ox86_VPMULU of wsize (* Parallel 32-bit → 64-bit multiplication *)
| Ox86_VPEXTR of wsize (* Element extraction from a 128-bit vector *)
| Ox86_VPINSR of velem (* Insert element into a 128-bit vector *)

| Ox86_VPSLL of velem & wsize (* Parallel shift left logical over 128/256-bit vectors *)
| Ox86_VPSRL of velem & wsize (* Parallel shift right logical over 128/256-bit vectors *)
| Ox86_VPSRA of velem & wsize (* Parallel shift right arithmetic over 128/256-bit vectors *)
| Ox86_VPSLLV of velem & wsize (* Parallel variable shift left logical over 128/256-bit vectors *)
| Ox86_VPSRLV of velem & wsize (* Parallel variable shift right logical over 128/256-bit vectors *)
| Ox86_VPSLLDQ of wsize (* Shift double quadword left logical *)
| Ox86_VPSRLDQ of wsize (* Shift double quadword right logical *)
| Ox86_VPSHUFB of wsize (* Shuffle bytes *)
| Ox86_VPSHUFHW of wsize (* Shuffle high 16-bit words *)
| Ox86_VPSHUFLW of wsize (* Shuffle low 16-bit words *)
| Ox86_VPSHUFD of wsize (* Shuffle 32-bit words *)
| Ox86_VPUNPCKH of velem & wsize (* Unpack High Data *)
| Ox86_VPUNPCKL of velem & wsize (* Unpack Low Data *)
| Ox86_VPBLENDD of wsize (* Blend 32-bit words *)
| Ox86_VPBROADCAST of velem & wsize (* Load integer and broadcast *)
| Ox86_VBROADCASTI128 (* Load integer and broadcast *)
| Ox86_VEXTRACTI128 (* Extract 128-bit value from a 256-bit vector *)
| Ox86_VINSERTI128 (* Insert a 128-bit element into a 256-bit vector *)
| Ox86_VPERM2I128 (* Permutation of 128-bit words *)
| Ox86_VPERMQ (* Permutation of 64-bit words *)
.

Scheme Equality for x86_instr_t.
Lemma x86_instr_t_eq_axiom : Equality.axiom x86_instr_t_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_x86_instr_t_dec_bl.
  by apply: internal_x86_instr_t_dec_lb.
Qed.

Definition x86_instr_t_eqMixin     := Equality.Mixin x86_instr_t_eq_axiom.
Canonical  x86_instr_t_eqType      := Eval hnf in EqType x86_instr_t x86_instr_t_eqMixin.

Definition pp_s     (s: string)                         (_: unit) : string := s.
Definition pp_sz    (s: string) (sz: wsize)             (_: unit) : string := s ++ " " ++ string_of_wsize sz.
Definition pp_sz_sz (s: string) (sz sz': wsize)         (_: unit) : string := s ++ " " ++ string_of_wsize sz ++ " " ++ string_of_wsize sz'.
Definition pp_ve_sz (s: string) (ve: velem) (sz: wsize) (_: unit) : string := s ++ " " ++ string_of_velem ve ++ " " ++ string_of_wsize sz.
Definition pp_ve    (s: string) (ve: velem)             (_: unit)   : string := s ++ " " ++ string_of_velem ve.

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

Definition SF_of_word sz (w : word sz) :=
  msb w.

Definition PF_of_word sz (w : word sz) :=
  lsb w.

Definition ZF_of_word sz (w : word sz) :=
  w == 0%R.

(* -------------------------------------------------------------------- *)
  (*  OF; CF; SF;    PF;    ZF  *)
Definition rflags_of_bwop sz (w : word sz) :=
  (*  OF;  CF;    SF;           PF;           ZF  *)
  ( false, false, SF_of_word w, PF_of_word w, ZF_of_word w).

(* -------------------------------------------------------------------- *)
(*  OF; CF ;SF; PF; ZF  *)
Definition rflags_of_aluop sz (w : word sz) (vu vs : Z) :=
  (*  OF;             CF;                SF;           PF;           ZF  *)
  ( wsigned  w != vs, wunsigned w != vu, SF_of_word w, PF_of_word w, ZF_of_word w ).

(* -------------------------------------------------------------------- *)
Definition rflags_of_mul (ov : bool) :=
  (*  OF; CF; SF;    PF;    ZF  *)
  (   ov, ov, sbool, sbool, sbool ).
Check rflags_of_mul.

(* -------------------------------------------------------------------- *)

Definition rflags_of_div :=
  (*  OF;    CF;    SF;    PF;    ZF  *)
  (   sbool, sbool, sbool, sbool, sbool ).

(* -------------------------------------------------------------------- *)
(*  OF; SF; PF; ZF  *)
Definition rflags_of_aluop_nocf sz (w : word sz) (vs : Z) :=
  (*  OF                 SF          ; PF          ; ZF          ] *)
  (   wsigned   w != vs, SF_of_word w, PF_of_word w, ZF_of_word w ).

(* Definition flags_w (bs:seq bool) sz (w: word sz) :=
  ok ((map Vbool bs) ++ [:: Vword w]).
 *)
(* Definition rflags_of_aluop_w sz (w : word sz) (vu vs : Z) : exec values :=
  flags_w (rflags_of_aluop w vu vs) w.
 *)
(* Definition rflags_of_aluop_nocf_w sz (w : word sz) (vs : Z) : exec values :=
  flags_w (rflags_of_aluop_nocf w vs) w.
 *)
(* Definition rflags_of_bwop_w sz (w : word sz) : exec values :=
  flags_w (rflags_of_bwop w) w.
 *)
(* Definition vbools bs : exec values := ok (List.map Vbool bs).
 *)
(* -------------------------------------------------------------------- *)



Definition x86_MOV sz (x: word sz) : exec (word sz) :=
  Let _ := check_size_8_64 sz in
  ok x.

Notation mk_instr str tin tout semi :=
  {| str := str; tin := tin; tout := tout; semi := semi; tin_narr := refl_equal |}.

Definition mk_instr_w name semi sz :=
  mk_instr (pp_sz name sz) (w_ty sz) (w_ty sz) (semi sz).

Definition mk_instr_w2_b5w name semi sz :=
  mk_instr (pp_sz name sz) (w2_ty sz sz) (b5w_ty sz) (semi sz).

Definition Ox86_MOV_instr := mk_instr_w "Ox86_MOV" x86_MOV.

(*Definition Ox86_ADD_instr := mk_instr_w2_b5w "Ox86_ADD" x86_ADD.
Definition Ox86_SUB_instr := mk_instr_w2_b5w "Ox86_SUB" x86_SUB.
*)
(*
Definition Ox86_MOVSX_instr sz sz'      := {| str:= pp_sz_sz "Ox86_MOVSX" sz sz';    tout:= w_ty sz ;     tin:= w_ty sz' |}.
Definition Ox86_MOVZX_instr sz sz'      := {| str:= pp_sz_sz "Ox86_MOVZX" sz sz';    tout:= w_ty sz ;     tin:= w_ty sz' |}.
Definition Ox86_MOVZX32_instr           := {| str:= pp_s  "Ox86_MOVZX32";            tout:= w64_ty;       tin:= w32_ty |}.
Definition Ox86_CMOVcc_instr sz         := {| str:= pp_sz "Ox86_CMOVcc" sz;          tout:= w_ty sz ;     tin:= bw2_ty sz |}.
Definition Ox86_ADD_instr sz            := {| str:= pp_sz "Ox86_ADD" sz;             tout:= b5w_ty sz;    tin:= w2_ty sz sz |}.
Definition Ox86_SUB_instr sz            := {| str:= pp_sz "Ox86_SUB" sz;             tout:= b5w_ty sz;    tin:= w2_ty sz sz |}.
Definition Ox86_MUL_instr sz            := {| str:= pp_sz "Ox86_MUL" sz;             tout:= b5w2_ty sz;   tin:= w2_ty sz sz |}.
Definition Ox86_IMUL_instr sz           := {| str:= pp_sz "Ox86_IMUL" sz;            tout:= b5w2_ty sz;   tin:= w2_ty sz sz |}.
Definition Ox86_IMULt_instr sz          := {| str:= pp_sz "Ox86_IMULt" sz;           tout:= b5w_ty sz;    tin:= w2_ty sz sz |}.
Definition Ox86_IMULtimm_instr sz       := {| str:= pp_sz "Ox86_IMULtimm" sz;        tout:= b5w_ty sz;    tin:= w2_ty sz sz |}.
Definition Ox86_DIV_instr sz            := {| str:= pp_sz "Ox86_DIV" sz;             tout:= b5w2_ty sz;   tin:= w3_ty sz |}.
Definition Ox86_IDIV_instr sz           := {| str:= pp_sz "Ox86_IDIV" sz;            tout:= b5w2_ty sz;   tin:= w3_ty sz |}.
Definition Ox86_CQO_instr sz            := {| str:= pp_sz "Ox86_CQO" sz;             tout:= w_ty sz;      tin:= w_ty sz |}.
Definition Ox86_ADC_instr sz            := {| str:= pp_sz "Ox86_ADC" sz;             tout:= b5w_ty sz;    tin:= w2b_ty sz sz |}.
Definition Ox86_SBB_instr sz            := {| str:= pp_sz "Ox86_SBB" sz;             tout:= b5w_ty sz;    tin:= w2b_ty sz sz |}.
Definition Ox86_NEG_instr sz            := {| str:= pp_sz "Ox86_NEG" sz;             tout:= b5w_ty sz;    tin:= w_ty sz |}.
Definition Ox86_INC_instr sz            := {| str:= pp_sz "Ox86_INC" sz;             tout:= b4w_ty sz;    tin:= w_ty sz |}.
Definition Ox86_DEC_instr sz            := {| str:= pp_sz "Ox86_DEC" sz;             tout:= b4w_ty sz;    tin:= w_ty sz |}.
Definition Ox86_SETcc_instr             := {| str:= pp_s "Ox86_SETcc";               tout:= w_ty U8;      tin:= b_ty |}.
Definition Ox86_BT_instr sz             := {| str:= pp_sz "Ox86_BT" sz;              tout:= b_ty;         tin:= w2_ty sz sz |}.
Definition Ox86_LEA_instr sz            := {| str:= pp_sz "Ox86_LEA" sz;             tout:= w_ty sz;      tin:= w4_ty sz |}.
Definition Ox86_TEST_instr sz           := {| str:= pp_sz "Ox86_TEST" sz;            tout:= b5_ty;        tin:= w2_ty sz sz |}.
Definition Ox86_CMP_instr sz            := {| str:= pp_sz "Ox86_CMP" sz;             tout:= b5_ty;        tin:= w2_ty sz sz |}.
Definition Ox86_AND_instr sz            := {| str:= pp_sz "Ox86_AND" sz;             tout:= b5w_ty sz;    tin:= w2_ty sz sz |}.
Definition Ox86_ANDN_instr sz           := {| str:= pp_sz "Ox86_ANDN" sz;            tout:= b5w_ty sz;    tin:= w2_ty sz sz |}.
Definition Ox86_OR_instr sz             := {| str:= pp_sz "Ox86_OR" sz;              tout:= b5w_ty sz;    tin:= w2_ty sz sz |}.
Definition Ox86_XOR_instr sz            := {| str:= pp_sz "Ox86_XOR" sz;             tout:= b5w_ty sz;    tin:= w2_ty sz sz |}.
Definition Ox86_NOT_instr sz            := {| str:= pp_sz "Ox86_NOT" sz;             tout:= w_ty sz;      tin:= w_ty sz |}.
Definition Ox86_ROR_instr sz            := {| str:= pp_sz "Ox86_ROR" sz;             tout:= b2w_ty sz;    tin:= ww8_ty sz |}.
Definition Ox86_ROL_instr sz            := {| str:= pp_sz "Ox86_ROL" sz;             tout:= b2w_ty sz;    tin:= ww8_ty sz |}.
Definition Ox86_SHL_instr sz            := {| str:= pp_sz "Ox86_SHL" sz;             tout:= b5w_ty sz;    tin:= ww8_ty sz |}.
Definition Ox86_SHR_instr sz            := {| str:= pp_sz "Ox86_SHR" sz;             tout:= b5w_ty sz;    tin:= ww8_ty sz |}.
Definition Ox86_SAR_instr sz            := {| str:= pp_sz "Ox86_SAR" sz;             tout:= b5w_ty sz;    tin:= ww8_ty sz |}.
Definition Ox86_SHLD_instr sz           := {| str:= pp_sz "Ox86_SHLD" sz;            tout:= b5w_ty sz;    tin:= w2w8_ty sz |}.
Definition Ox86_SHRD_instr sz           := {| str:= pp_sz "Ox86_SHRD" sz;            tout:= b5w_ty sz;    tin:= w2w8_ty sz |}.
Definition Ox86_BSWAP_instr sz          := {| str:= pp_sz "Ox86_BSWAP" sz;           tout:= w_ty sz;      tin:= w_ty sz |}.
Definition Ox86_MOVD_instr sz           := {| str:= pp_sz "Ox86_MOVD" sz;            tout:= w128_ty;      tin:= w_ty sz |}.
Definition Ox86_VMOVDQU_instr sz        := {| str:= pp_sz "Ox86_VMOVDQU" sz;         tout:= w_ty sz;      tin:= w_ty sz |}.
Definition Ox86_VPAND_instr sz          := {| str:= pp_sz "Ox86_VPAND" sz;           tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPANDN_instr sz         := {| str:= pp_sz "Ox86_VPANDN" sz;          tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPOR_instr sz           := {| str:= pp_sz "Ox86_VPOR" sz;            tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPXOR_instr sz          := {| str:= pp_sz "Ox86_VPXOR" sz;           tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPADD_instr ve sz       := {| str:= pp_ve_sz "Ox86_VPADD" ve sz;     tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPSUB_instr ve sz       := {| str:= pp_ve_sz "Ox86_VPSUB" ve sz;     tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPMULL_instr ve sz      := {| str:= pp_ve_sz "Ox86_VPMULL" ve sz;    tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPMULU_instr sz         := {| str:= pp_sz "Ox86_VPMULU" sz ;         tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPEXTR_instr ve         := {| str:= pp_sz "Ox86_VPEXTR" ve ;         tout:= w_ty ve;      tin:= w128w8_ty |}.
Definition Ox86_VPINSR_instr ve         := {| str:= pp_ve "Ox86_VPINSR" ve ;         tout:= w128_ty;      tin:= w128ww8_ty ve |}.
Definition Ox86_VPSLL_instr ve sz       := {| str:= pp_ve_sz "Ox86_VPSLL" ve sz ;    tout:= w_ty sz;      tin:= ww8_ty sz |}.
Definition Ox86_VPSRL_instr ve sz       := {| str:= pp_ve_sz "Ox86_VPSRL" ve sz ;    tout:= w_ty sz;      tin:= ww8_ty sz |}.
Definition Ox86_VPSRA_instr ve sz       := {| str:= pp_ve_sz "Ox86_VPSRA" ve sz ;    tout:= w_ty sz;      tin:= ww8_ty sz |}.
Definition Ox86_VPSLLV_instr ve sz      := {| str:= pp_ve_sz "Ox86_VPSLLV" ve sz ;   tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPSRLV_instr ve sz      := {| str:= pp_ve_sz "Ox86_VPSRLV" ve sz ;   tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPSLLDQ_instr sz        := {| str:= pp_sz "Ox86_VPSLLDQ" sz ;        tout:= w_ty sz;      tin:= ww8_ty sz |}.
Definition Ox86_VPSRLDQ_instr sz        := {| str:= pp_sz "Ox86_VPSRLDQ" sz ;        tout:= w_ty sz;      tin:= ww8_ty sz |}.
Definition Ox86_VPSHUFB_instr sz        := {| str:= pp_sz "Ox86_VPSHUFB" sz ;        tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPSHUFHW_instr sz       := {| str:= pp_sz "Ox86_VPSHUFHW" sz ;       tout:= w_ty sz;      tin:= ww8_ty sz |}.
Definition Ox86_VPSHUFLW_instr sz       := {| str:= pp_sz "Ox86_VPSHUFLW" sz ;       tout:= w_ty sz;      tin:= ww8_ty sz |}.
Definition Ox86_VPSHUFD_instr sz        := {| str:= pp_sz "Ox86_VPSHUFD" sz ;        tout:= w_ty sz;      tin:= ww8_ty sz |}.
Definition Ox86_VPUNPCKH_instr ve sz    := {| str:= pp_ve_sz "Ox86_VPUNPCKH" ve sz;  tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPUNPCKL_instr ve sz    := {| str:= pp_ve_sz "Ox86_VPUNPCKL" ve sz;  tout:= w_ty sz;      tin:= w2_ty sz sz |}.
Definition Ox86_VPBLENDD_instr sz       := {| str:= pp_sz "Ox86_VPBLENDD" sz;        tout:= w_ty sz;      tin:= w2w8_ty sz |}.
Definition Ox86_VPBROADCAST_instr ve sz := {| str:= pp_ve_sz "Ox86_VPBROADCAST" ve sz; tout:= w_ty sz;    tin:= w_ty ve |}.
Definition Ox86_VBROADCASTI128_instr    := {| str:= pp_s "Ox86_VBROADCASTI128" ;     tout:= w256_ty;      tin:= w128_ty |}.
Definition Ox86_VEXTRACTI128_instr      := {| str:= pp_s "Ox86_VEXTRACTI128" ;       tout:= w128_ty;      tin:= w256w8_ty |}.
Definition Ox86_VINSERTI128_instr       := {| str:= pp_s "Ox86_VINSERTI128" ;        tout:= w256_ty;      tin:= w256w128w8_ty |}.
Definition Ox86_VPERM2I128_instr        := {| str:= pp_s "Ox86_VPERM2I128" ;         tout:= w256_ty;      tin:= w256x2w8_ty |}.
Definition Ox86_VPERMQ_instr            := {| str:= pp_s "Ox86_VPERMQ" ;             tout:= w256_ty;      tin:= w256w8_ty |}. *)



(*
  | Ox86_MOV sz => app_w sz (@x86_MOV sz)
  | Ox86_MOVSX sz sz' => app_w sz' (@x86_MOVSX sz sz')
  | Ox86_MOVZX sz sz' => app_w sz' (@x86_MOVZX sz sz')
  | Ox86_MOVZX32 => app_w U32 (λ x : u32, ok [:: Vword (zero_extend U64 x) ])
  | Ox86_CMOVcc sz => (fun v => match v with
    | [:: v1; v2; v3] =>
      Let _ := check_size_16_64 sz in
      Let b := to_bool v1 in
      Let w2 := to_word sz v2 in
      Let w3 := to_word sz v3 in
      if b then (ok [:: Vword w2])
      else (ok [:: Vword w3])
    | _ => type_error end)
  | Ox86_ADD sz => app_ww sz x86_add
  | Ox86_SUB sz => app_ww sz x86_sub
  | Ox86_MUL sz => app_ww sz x86_mul
  | Ox86_IMUL sz => app_ww sz x86_imul
  | Ox86_IMULt sz => app_ww sz x86_imult
  | Ox86_IMULtimm sz => app_ww sz x86_imult
  | Ox86_DIV sz => app_www sz x86_div
  | Ox86_IDIV sz => app_www sz x86_idiv
  | Ox86_CQO sz => app_w sz x86_cqo
  | Ox86_ADC sz => app_wwb sz x86_adc
  | Ox86_SBB sz => app_wwb sz x86_sbb
  | Ox86_NEG sz => app_w sz x86_neg
  | Ox86_INC sz => app_w sz x86_inc
  | Ox86_DEC sz => app_w sz x86_dec
  | Ox86_SETcc => app_b x86_setcc
  | Ox86_BT sz => app_ww sz x86_bt
  | Ox86_LEA sz => app_w4 sz x86_lea
  | Ox86_TEST sz => app_ww sz x86_test
  | Ox86_CMP sz => app_ww sz x86_cmp
  | Ox86_AND sz => app_ww sz x86_and
  | Ox86_ANDN sz => app_ww sz x86_andn
  | Ox86_OR sz => app_ww sz x86_or
  | Ox86_XOR sz => app_ww sz x86_xor
  | Ox86_NOT sz => app_w sz x86_not
  | Ox86_ROL sz => app_w8 sz x86_rol
  | Ox86_ROR sz => app_w8 sz x86_ror
  | Ox86_SHL sz => app_w8 sz x86_shl
  | Ox86_SHR sz => app_w8 sz x86_shr
  | Ox86_SAR sz => app_w8 sz x86_sar
  | Ox86_SHLD sz => app_ww8 sz x86_shld
  | Ox86_SHRD sz => app_ww8 sz x86_shrd
  | Ox86_BSWAP sz => app_w sz x86_bswap
  | Ox86_MOVD sz => app_w sz x86_movd
  | Ox86_VMOVDQU sz => app_sopn [:: sword sz ] (λ x,
                                                Let _ := check_size_128_256 sz in
                                                ok [:: Vword x])
  | Ox86_VPAND sz => app_ww sz x86_vpand
  | Ox86_VPANDN sz => app_ww sz x86_vpandn
  | Ox86_VPOR sz => app_ww sz x86_vpor
  | Ox86_VPXOR sz => app_ww sz x86_vpxor
  | Ox86_VPADD ve sz => app_ww sz (x86_vpadd ve)
  | Ox86_VPSUB ve sz => app_ww sz (x86_vpsub ve)
  | Ox86_VPMULL ve sz => app_ww sz (x86_vpmull ve)
  | Ox86_VPMULU sz => app_ww sz x86_vpmulu
  | Ox86_VPEXTR ve => app_w8 U128 (x86_vpextr ve)
  | Ox86_VPINSR ve => app_sopn [:: sword128 ; sword ve ; sword8 ] (x86_vpinsr ve)
  | Ox86_VPSLL ve sz => app_w8 sz (x86_vpsll ve)
  | Ox86_VPSRL ve sz => app_w8 sz (x86_vpsrl ve)
  | Ox86_VPSRA ve sz => app_w8 sz (x86_vpsra ve)
  | Ox86_VPSLLV ve sz => app_ww sz (x86_vpsllv ve)
  | Ox86_VPSRLV ve sz => app_ww sz (x86_vpsrlv ve)
  | Ox86_VPSLLDQ sz => app_w8 sz x86_vpslldq
  | Ox86_VPSRLDQ sz => app_w8 sz x86_vpsrldq
  | Ox86_VPSHUFB sz => app_ww sz x86_vpshufb
  | Ox86_VPSHUFHW sz => app_w8 sz x86_vpshufhw
  | Ox86_VPSHUFLW sz => app_w8 sz x86_vpshuflw
  | Ox86_VPSHUFD sz => app_w8 sz x86_vpshufd
  | Ox86_VPUNPCKH ve sz => app_ww sz (x86_vpunpckh ve)
  | Ox86_VPUNPCKL ve sz => app_ww sz (x86_vpunpckl ve)
  | Ox86_VPBLENDD sz => app_ww8 sz x86_vpblendd
  | Ox86_VPBROADCAST ve sz => app_w ve (x86_vpbroadcast sz)
  | Ox86_VBROADCASTI128 => app_w U128 (x86_vpbroadcast U256)
  | Ox86_VEXTRACTI128 => app_w8 U256 x86_vextracti128
  | Ox86_VINSERTI128 => app_sopn [:: sword256 ; sword128 ; sword8 ] x86_vinserti128
  | Ox86_VPERM2I128 => app_ww8 U256 x86_vperm2i128
  | Ox86_VPERMQ => app_w8 U256 x86_vpermq
  end.
 *)


Definition map_instruction o : Instruction :=
  match o with
  | Ox86_MOV sz             => Ox86_MOV_instr sz
  | _ => Ox86_MOV_instr U8
(*  | Ox86_MOVSX sz sz'       => Ox86_MOVSX_instr sz sz'
  | Ox86_MOVZX sz sz'       => Ox86_MOVZX_instr sz sz'
  | Ox86_CMOVcc sz          => Ox86_CMOVcc_instr sz
  | Ox86_BSWAP sz           => Ox86_BSWAP_instr sz
  | Ox86_CQO sz             => Ox86_CQO_instr sz
  | Ox86_MOVZX32            => Ox86_MOVZX32_instr
  | Ox86_ADD sz             => Ox86_ADD_instr sz
  | Ox86_SUB sz             => Ox86_SUB_instr sz
  | Ox86_MUL sz             => Ox86_MUL_instr sz
  | Ox86_IMUL sz            => Ox86_IMUL_instr sz
  | Ox86_IMULt sz           => Ox86_IMULt_instr sz
  | Ox86_IMULtimm sz        => Ox86_IMULtimm_instr sz
  | Ox86_DIV sz             => Ox86_DIV_instr sz
  | Ox86_IDIV sz            => Ox86_IDIV_instr sz
  | Ox86_ADC sz             => Ox86_ADC_instr sz
  | Ox86_SBB sz             => Ox86_SBB_instr sz
  | Ox86_NEG sz             => Ox86_NEG_instr sz
  | Ox86_INC sz             => Ox86_INC_instr sz
  | Ox86_DEC sz             => Ox86_DEC_instr sz
  | Ox86_SETcc              => Ox86_SETcc_instr
  | Ox86_BT sz              => Ox86_BT_instr sz
  | Ox86_LEA sz             => Ox86_LEA_instr sz
  | Ox86_TEST sz            => Ox86_TEST_instr sz
  | Ox86_CMP sz             => Ox86_CMP_instr sz
  | Ox86_AND sz             => Ox86_AND_instr sz
  | Ox86_ANDN sz            => Ox86_ANDN_instr sz
  | Ox86_OR sz              => Ox86_OR_instr sz
  | Ox86_XOR sz             => Ox86_XOR_instr sz
  | Ox86_NOT sz             => Ox86_NOT_instr sz
  | Ox86_ROL sz             => Ox86_ROL_instr sz
  | Ox86_ROR sz             => Ox86_ROR_instr sz
  | Ox86_SHL sz             => Ox86_SHL_instr sz
  | Ox86_SHR sz             => Ox86_SHR_instr sz
  | Ox86_SAR sz             => Ox86_SAR_instr sz
  | Ox86_SHLD sz            => Ox86_SHLD_instr sz
  | Ox86_SHRD sz            => Ox86_SHRD_instr sz
  | Ox86_MOVD sz            => Ox86_MOVD_instr sz
  | Ox86_VPINSR sz          => Ox86_VPINSR_instr sz
  | Ox86_VEXTRACTI128       => Ox86_VEXTRACTI128_instr
  | Ox86_VMOVDQU sz         => Ox86_VMOVDQU_instr sz
  | Ox86_VPAND sz           => Ox86_VPAND_instr sz
  | Ox86_VPANDN sz          => Ox86_VPANDN_instr sz
  | Ox86_VPOR sz            => Ox86_VPOR_instr sz
  | Ox86_VPXOR sz           => Ox86_VPXOR_instr sz
  | Ox86_VPADD sz sz'       => Ox86_VPADD_instr sz sz'
  | Ox86_VPSUB sz sz'       => Ox86_VPSUB_instr sz sz'
  | Ox86_VPMULL sz sz'      => Ox86_VPMULL_instr sz sz'
  | Ox86_VPMULU sz          => Ox86_VPMULU_instr sz
  | Ox86_VPSLL sz sz'       => Ox86_VPSLL_instr sz sz'
  | Ox86_VPSRL sz sz'       => Ox86_VPSRL_instr sz sz'
  | Ox86_VPSRA sz sz'       => Ox86_VPSRA_instr sz sz'
  | Ox86_VPSLLV sz sz'      => Ox86_VPSLLV_instr sz sz'
  | Ox86_VPSRLV sz sz'      => Ox86_VPSRLV_instr sz sz'
  | Ox86_VPSLLDQ sz         => Ox86_VPSLLDQ_instr sz
  | Ox86_VPSRLDQ sz         => Ox86_VPSRLDQ_instr sz
  | Ox86_VPSHUFB sz         => Ox86_VPSHUFB_instr sz
  | Ox86_VPSHUFHW sz        => Ox86_VPSHUFHW_instr sz
  | Ox86_VPSHUFLW sz        => Ox86_VPSHUFLW_instr sz
  | Ox86_VPSHUFD sz         => Ox86_VPSHUFD_instr sz
  | Ox86_VPUNPCKH sz sz'    => Ox86_VPUNPCKH_instr sz sz'
  | Ox86_VPUNPCKL sz sz'    => Ox86_VPUNPCKL_instr sz sz'
  | Ox86_VPBLENDD sz        => Ox86_VPBLENDD_instr sz
  | Ox86_VPBROADCAST sz sz' => Ox86_VPBROADCAST_instr sz sz'
  | Ox86_VBROADCASTI128     => Ox86_VBROADCASTI128_instr
  | Ox86_VPERM2I128         => Ox86_VPERM2I128_instr
  | Ox86_VPERMQ             => Ox86_VPERMQ_instr
  | Ox86_VINSERTI128        => Ox86_VINSERTI128_instr
  | Ox86_VPEXTR ve          => Ox86_VPEXTR_instr ve *)
  end.

Definition string_of_x86_instr_t o : string :=
  str (map_instruction o) tt.

Definition x86_instr_t_tout o :=
  tout (map_instruction o).

Definition x86_instr_t_tin o :=
  tin (map_instruction o).

Definition x86_instr_t_sem o :=
  semi (map_instruction o).
