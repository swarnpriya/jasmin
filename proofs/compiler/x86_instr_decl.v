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
Require Import ZArith utils strings low_memory word sem_type global oseq.
Import Utf8 Relation_Operators.
Import Memory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import x86_decl.

(* -------------------------------------------------------------------- *)

Variant asm_op : Type := 
  (* Data transfert *)
| MOV    of wsize              (* copy *)
| MOVSX  of wsize & wsize      (* sign-extend *)
| MOVZX  of wsize & wsize      (* zero-extend *)
| CMOVcc of wsize              (* conditional copy *)

  (* Arithmetic *)
| ADD    of wsize                  (* add unsigned / signed *)
| SUB    of wsize                  (* sub unsigned / signed *)
| MUL    of wsize                  (* mul unsigned *)
| IMUL   of wsize                             (* mul signed with truncation *)
| IMULr  of wsize   (* oprd * oprd *)         (* mul signed with truncation *)
| IMULri of wsize   (* oprd * oprd * imm *)   (* mul signed with truncation *)

| DIV    of wsize                        (* div unsigned *)
| IDIV   of wsize                        (* div   signed *)
| CQO    of wsize                               (* CWD CDQ CQO: allows sign extention in many words *)
| ADC    of wsize                 (* add with carry *)
| SBB    of wsize                 (* sub with borrow *)

| NEG	   of wsize 	                      (* negation *)

| INC    of wsize                         (* increment *)
| DEC    of wsize                         (* decrement *)

  (* Flag *)
| SETcc                           (* Set byte on condition *)
| BT     of wsize                  (* Bit test, sets result to CF *)

  (* Pointer arithmetic *)
| LEA    of wsize              (* Load Effective Address *)

  (* Comparison *)
| TEST   of wsize                  (* Bit-wise logical and CMP *)
| CMP    of wsize                  (* Signed sub CMP *)


  (* Bitwise logical instruction *)
| AND    of wsize  (* bit-wise and *)
| ANDN   of wsize  (* bit-wise andn *)
| OR     of wsize  (* bit-wise or  *)
| XOR    of wsize  (* bit-wise xor *)
| NOT    of wsize  (* bit-wise not *)

  (* Bit shifts *)
| ROR    of wsize    (* rotation / right *)
| ROL    of wsize    (* rotation / left *)
| SHL    of wsize    (* unsigned / left  *)
| SHR    of wsize    (* unsigned / right *)
| SAL    of wsize    (*   signed / left; synonym of SHL *)
| SAR    of wsize    (*   signed / right *)
| SHLD   of wsize    (* unsigned (double) / left *)
| SHRD   of wsize    (* unsigned (double) / right *)

| BSWAP  of wsize                     (* byte swap *)

  (* SSE instructions *)
| MOVD     of wsize 
| VMOVDQU  `(wsize) 
| VPAND    `(wsize) 
| VPANDN   `(wsize) 
| VPOR     `(wsize) 
| VPXOR    `(wsize) 
| VPADD    `(velem) `(wsize) 
| VPSUB    `(velem) `(wsize) 
| VPMULL   `(velem) `(wsize) 
| VPMULU   `(wsize) 
| VPEXTR   `(wsize)
| VPINSR   `(velem) 
| VPSLL    `(velem) `(wsize) 
| VPSRL    `(velem) `(wsize) 
| VPSRA    `(velem) `(wsize) 
| VPSLLV   `(velem) `(wsize) 
| VPSRLV   `(velem) `(wsize) 
| VPSLLDQ  `(wsize) 
| VPSRLDQ  `(wsize) 
| VPSHUFB  `(wsize) 
| VPSHUFD  `(wsize)
| VPSHUFHW `(wsize)
| VPSHUFLW `(wsize)
| VPBLENDD `(wsize) 
| VPBROADCAST of velem & wsize 
| VBROADCASTI128 
| VPUNPCKH `(velem) `(wsize) 
| VPUNPCKL `(velem) `(wsize) 
| VEXTRACTI128 
| VINSERTI128 
| VPERM2I128 
| VPERMQ 
.

(* ----------------------------------------------------------------------------- *)
(* TODO move in wsize *)
Definition pp_s     (s: string)                         (_: unit) : string := s.
Definition pp_sz    (s: string) (sz: wsize)             (_: unit) : string := s ++ " " ++ string_of_wsize sz.
Definition pp_sz_sz (s: string) (sz sz': wsize)         (_: unit) : string := s ++ " " ++ string_of_wsize sz ++ " " ++ string_of_wsize sz'.
Definition pp_ve_sz (s: string) (ve: velem) (sz: wsize) (_: unit) : string := s ++ " " ++ string_of_velem ve ++ " " ++ string_of_wsize sz.
Definition pp_ve    (s: string) (ve: velem)             (_: unit)   : string := s ++ " " ++ string_of_velem ve.

(* ----------------------------------------------------------------------------- *)
Notation xword8   := (xword U8).
Notation xword16  := (xword U16).
Notation xword32  := (xword U32).
Notation xword64  := (xword U64).
Notation xword128 := (xword U128).
Notation xword256 := (xword U256).

Definition b_ty             := [:: xbool].
Definition b4_ty            := [:: xbool; xbool; xbool; xbool].
Definition b5_ty            := [:: xbool; xbool; xbool; xbool; xbool].

Definition bw_ty    sz      := [:: xbool; xword sz].
Definition bw2_ty   sz      := [:: xbool; xword sz; xword sz].
Definition b2w_ty   sz      := [:: xbool; xbool; xword sz].
Definition b4w_ty   sz      := [:: xbool; xbool; xbool; xbool; xword sz].
Definition b5w_ty   sz      := [:: xbool; xbool; xbool; xbool; xbool; xword sz].
Definition b5w2_ty  sz      := [:: xbool; xbool; xbool; xbool; xbool; xword sz; xword sz].

Definition w_ty     sz      := [:: xword sz].
Definition w2_ty    sz sz'  := [:: xword sz; xword sz'].
Definition w3_ty    sz      := [:: xword sz; xword sz; xword sz].
Definition w4_ty    sz      := [:: xword sz; xword sz; xword sz; xword sz].
Definition w8_ty            := [:: xword8].
Definition w32_ty           := [:: xword32].
Definition w64_ty           := [:: xword64].
Definition w128_ty          := [:: xword128].
Definition w256_ty          := [:: xword256].

Definition w2b_ty   sz sz'  := [:: xword sz; xword sz'; xbool].
Definition ww8_ty   sz      := [:: xword sz; xword8].
Definition w2w8_ty   sz     := [:: xword sz; xword sz; xword8].
Definition w128w8_ty        := [:: xword128; xword8].
Definition w128ww8_ty sz    := [:: xword128; xword sz; xword8].
Definition w256w8_ty        := [:: xword256; xword8].
Definition w256w128w8_ty    := [:: xword256; xword128; xword8].
Definition w256x2w8_ty      := [:: xword256; xword256; xword8].

(* ----------------------------------------------------------------------------- *)

Notation mk_instr str_jas tin tout ain aout msb semi check wsizei := {|
  id_msb_flag := msb;
  id_in       := zip ain tin;
  id_out      := zip aout tout; 
  id_semi     := semi; 
  id_check    := check;
  id_str_jas  := str_jas;
  id_wsize    := wsizei; 
|}.

Notation mk_instr_w_w name semi sz msb ain aout check :=
  (mk_instr (pp_sz name sz) (w_ty sz) (w_ty sz) ain aout msb (semi sz) check sz) (only parsing).

Notation mk_instr_w_w' name semi szi szo msb ain aout check :=
  (mk_instr (pp_sz_sz name szo szi) (w_ty szi) (w_ty szo) ain aout msb (semi szi szo) check szi) (only parsing).

Definition mk_instr_w2_w2 name semi sz :=
  mk_instr (pp_sz name sz) (w2_ty sz sz) (w2_ty sz sz) (semi sz) sz.

Definition mk_instr_w2b_bw name semi sz :=
  mk_instr (pp_sz name sz) [::xword sz; xword sz; xbool] (xbool :: (w_ty sz)) 
   (fun x y c => let p := semi sz x y c in ok (Some p.1, p.2)) sz.

Definition mk_instr__b5w name semi sz :=
  mk_instr (pp_sz name sz) [::] (b5w_ty sz) (semi sz) sz.

Definition mk_instr_b_w name semi sz :=
  mk_instr (pp_sz name sz) (b_ty) (w_ty sz) (semi sz) sz.

Definition mk_instr_bw2_w name semi sz :=
  mk_instr (pp_sz name sz) (bw2_ty sz) (w_ty sz) (semi sz) sz.

Definition mk_instr_w_b5w name semi sz :=
  mk_instr (pp_sz name sz) (w_ty sz) (b5w_ty sz) (semi sz) sz.

Definition mk_instr_w_b4w name semi sz :=
  mk_instr (pp_sz name sz) (w_ty sz) (b4w_ty sz) (semi sz) sz.

Definition mk_instr_w2_b name semi sz :=
  mk_instr (pp_sz name sz) (w2_ty sz sz) (b_ty) (semi sz) sz.

Definition mk_instr_w2_b5 name semi sz :=
  mk_instr (pp_sz name sz) (w2_ty sz sz) (b5_ty) (semi sz) sz.

Definition mk_instr_w2_b5w name semi sz :=
  mk_instr (pp_sz name sz) (w2_ty sz sz) (b5w_ty sz) (semi sz) sz.

Definition mk_instr_w2b_b5w name semi sz :=
  mk_instr (pp_sz name sz) (w2b_ty sz sz) (b5w_ty sz) (semi sz) sz.

Definition mk_instr_w2_b5w2 name semi sz :=
  mk_instr (pp_sz name sz) (w2_ty sz sz) (b5w2_ty sz) (semi sz) sz.

Definition mk_instr_w3_b5w2 name semi sz :=
  mk_instr (pp_sz name sz) (w3_ty sz) (b5w2_ty sz) (semi sz) sz.

Definition mk_instr_w2_w name semi sz :=
  mk_instr (pp_sz name sz) (w2_ty sz sz) (w_ty sz) (semi sz) sz.

Definition mk_instr_w4_w name semi sz :=
  mk_instr (pp_sz name sz) (w4_ty sz) (w_ty sz) (semi sz) sz.

Definition mk_instr_ww8_w name semi sz :=
  mk_instr (pp_sz name sz) (ww8_ty sz) (w_ty sz) (semi sz) sz.

Definition mk_instr_ww8_b2w name semi sz :=
  mk_instr (pp_sz name sz) (ww8_ty sz) (b2w_ty sz) (semi sz) sz.

Definition mk_instr_ww8_b5w name semi sz :=
  mk_instr (pp_sz name sz) (ww8_ty sz) (b5w_ty sz) (semi sz) sz.

Definition mk_instr_w2w8_b5w name semi sz :=
  mk_instr (pp_sz name sz) (w2w8_ty sz) (b5w_ty sz) (semi sz) sz.

Definition mk_instr_w2w8_w name semi sz :=
  mk_instr (pp_sz name sz) (w2w8_ty sz) (w_ty sz) (semi sz) sz.

Definition mk_instr_w_w128 name semi sz :=
  mk_instr (pp_sz name sz) (w_ty sz) (w128_ty) (semi sz) sz.

Definition mk_instr_w128w8_w name semi sz :=
  mk_instr (pp_sz name sz) (w128w8_ty) (w_ty sz) (semi sz) sz.

Definition mk_ve_instr_w_w name semi ve sz :=
  mk_instr (pp_ve_sz name ve sz) (w_ty ve) (w_ty sz) (semi ve sz) sz.

Definition mk_ve_instr_w2_w name semi ve sz :=
  mk_instr (pp_ve_sz name ve sz) (w2_ty sz sz) (w_ty sz) (semi ve sz) sz.

Definition mk_ve_instr_ww8_w name semi ve sz :=
  mk_instr (pp_ve_sz name ve sz) (ww8_ty sz) (w_ty sz) (semi ve sz) sz.

(* -------------------------------------------------------------------- *)

Require Import x86_instr_t.
(* -------------------------------------------------------------------- *)

Definition check_opdr a1 := 
  match a1 with
  | Imm _ _ | Glob _ | Reg _  | Adr _  => true
  | _ => false
  end.
  
Definition check_ri a1 := 
  match a1 with
  | Imm _ _  | Reg _  => true
  | _ => false
  end.

Definition check2_regmemi (args: list asm_arg) := 
  match args with
  | [::Reg _; a1] => check_opdr a1
  | [::Adr _; a1] => check_ri a1
  | _               => false
  end.

Definition MOV_desc sz := 
  {| id_msb_flag := MSB_CLEAR; 
     id_in  := [:: (E sz 1, xword sz) ];
     id_out := [:: (E sz 0, xword sz) ];
     id_semi := @x86_MOV sz;
     id_check := check2_regmemi |}.

Definition instr_desc (o:asm_op) : instr_desc_t := 
  match o with
  | MOV sz => MOV_desc sz
  | _ => MOV_desc U8
  end.
