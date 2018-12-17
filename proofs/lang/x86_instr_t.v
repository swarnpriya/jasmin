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

Local Open Scope Z_scope.

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


(* ----------------------------------------------------------------------------- *)

Definition SF_of_word sz (w : word sz) :=
  msb w.

Definition PF_of_word sz (w : word sz) :=
  lsb w.

Definition ZF_of_word sz (w : word sz) :=
  w == 0%R.

(* -------------------------------------------------------------------- *)
  (*  OF; CF; SF;    PF;    ZF  *)
Definition rflags_of_bwop sz (w : word sz) : (sem_tuple b5_ty) :=
  (*  OF;  CF;    SF;           PF;           ZF  *)
  (:: Some false, Some false, Some (SF_of_word w), Some (PF_of_word w) & Some (ZF_of_word w)).

(* -------------------------------------------------------------------- *)
(*  OF; CF ;SF; PF; ZF  *)
Definition rflags_of_aluop sz (w : word sz) (vu vs : Z) : (sem_tuple b5_ty) :=
  (*  OF;             CF;                SF;           PF;           ZF  *)
  (:: Some (wsigned  w != vs), Some (wunsigned w != vu), Some (SF_of_word w), Some (PF_of_word w) & Some (ZF_of_word w )).

(* -------------------------------------------------------------------- *)
Definition rflags_of_mul (ov : bool) : (sem_tuple b5_ty) :=
  (*  OF; CF; SF;    PF;    ZF  *)
  (:: Some ov, Some ov, None, None & None).

(* -------------------------------------------------------------------- *)

Definition rflags_of_div : (sem_tuple b5_ty):=
  (*  OF;    CF;    SF;    PF;    ZF  *)
  (:: None, None, None, None & None).

(* -------------------------------------------------------------------- *)

Definition rflags_of_andn sz (w: word sz) : (sem_tuple b5_ty) :=
  (* OF ; CF ; SF ; PF ; ZF *)
  (:: Some false , Some false , Some (SF_of_word w) , None & Some (ZF_of_word w) ).

(* -------------------------------------------------------------------- *)

Definition rflags_None_w {sz} w : (sem_tuple (b5w_ty sz)):=
  (*  OF;    CF;    SF;    PF;    ZF  *)
  (:: None, None, None, None, None & w).


(* -------------------------------------------------------------------- *)
(*  OF; SF; PF; ZF  *)
Definition rflags_of_aluop_nocf sz (w : word sz) (vs : Z) : (sem_tuple b4_ty) :=
  (*  OF                 SF          ; PF          ; ZF          ] *)
  (:: Some (wsigned   w != vs), Some (SF_of_word w), Some (PF_of_word w) & Some (ZF_of_word w)).

Definition flags_w {l1} (bs: ltuple l1) {sz} (w: word sz):=
  (merge_tuple bs (w : sem_tuple (w_ty sz))).

Definition flags_w2 {l1} (bs: ltuple l1) {sz} w :=
  (merge_tuple bs (w : sem_tuple (w2_ty sz sz))).

Definition rflags_of_aluop_w sz (w : word sz) (vu vs : Z) :=
  flags_w (rflags_of_aluop w vu vs) w.

Definition rflags_of_aluop_nocf_w sz (w : word sz) (vs : Z) :=
  flags_w (rflags_of_aluop_nocf w vs) w.

Definition rflags_of_bwop_w sz (w : word sz) :=
  flags_w (rflags_of_bwop w) w.

(* -------------------------------------------------------------------- *)

Notation "'ex_tpl' A" := (exec (sem_tuple A)) (at level 200, only parsing).

Definition x86_MOV sz (x: word sz) : exec (word sz) :=
  Let _ := check_size_8_64 sz in
  ok x.

Definition x86_MOVSX szi szo (x: word szi) : ex_tpl (w_ty szo) :=
  Let _ :=
    match szi with
    | U8 => check_size_16_64 szo
    | U16 => check_size_32_64 szo
    | U32 => assert (szo == U64) ErrType
    | _ => type_error
    end in
  ok (sign_extend szo x).

Definition x86_MOVZX szi szo (x: word szi) : ex_tpl (w_ty szo) :=
  Let _ :=
    match szi with
    | U8 => check_size_16_64 szo
    | U16 => check_size_32_64 szo
    | _ => type_error
    end in
  ok (zero_extend szo x).

Definition x86_ADD sz (v1 v2 : word sz) : ex_tpl (b5w_ty sz) :=
  Let _ := check_size_8_64 sz in
  ok (rflags_of_aluop_w
    (v1 + v2)%R
    (wunsigned v1 + wunsigned v2)%Z
    (wsigned   v1 + wsigned   v2)%Z).

Definition x86_SUB sz (v1 v2 : word sz) : ex_tpl (b5w_ty sz) :=
  Let _ := check_size_8_64 sz in
  ok (rflags_of_aluop_w
    (v1 - v2)%R
    (wunsigned v1 - wunsigned v2)%Z
    (wsigned   v1 - wsigned   v2)%Z).

Definition x86_CMOVcc sz (b:bool) (w2 w3: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_16_64 sz in
  if b then (ok w2) else (ok w3).

Definition x86_MUL sz (v1 v2: word sz) : ex_tpl (b5w2_ty sz) :=
  Let _  := check_size_16_64 sz in
  let lo := (v1 * v2)%R in
  let hi := wmulhu v1 v2 in
  let ov := wdwordu hi lo in
  let ov := (ov >? wbase sz - 1)%Z in
  ok (flags_w2 (rflags_of_mul ov) (:: hi & lo)).

Definition x86_IMUL_overflow sz (hi lo: word sz) : bool :=
  let ov := wdwords hi lo in
  (ov <? -wbase sz)%Z || (ov >? wbase sz - 1)%Z.

Definition x86_IMUL sz (v1 v2: word sz) : ex_tpl (b5w2_ty sz) :=
  Let _  := check_size_16_64 sz in
  let lo := (v1 * v2)%R in
  let hi := wmulhs v1 v2 in
  let ov := x86_IMUL_overflow hi lo in
  ok (flags_w2 (rflags_of_mul ov) (:: hi & lo)).

Definition x86_IMULt sz (v1 v2: word sz) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_16_64 sz in
  let lo := (v1 * v2)%R in
  let hi := wmulhs v1 v2 in
  let ov := x86_IMUL_overflow hi lo in
  ok (flags_w (rflags_of_mul ov) lo).

Definition x86_DIV sz (hi lo dv: word sz) : ex_tpl (b5w2_ty sz) :=
  Let _  := check_size_16_64 sz in
  let dd := wdwordu hi lo in
  let dv := wunsigned dv in
  let q  := (dd  /  dv)%Z in
  let r  := (dd mod dv)%Z in
  let ov := (q >? wmax_unsigned sz)%Z in

  if (dv == 0)%Z || ov then type_error else
  ok (flags_w2 (rflags_of_div) (:: (wrepr sz q) & (wrepr sz r))).

Definition x86_IDIV sz (hi lo dv: word sz) : ex_tpl (b5w2_ty sz) :=
  Let _  := check_size_16_64 sz in
  let dd := wdwords hi lo in
  let dv := wsigned dv in
  let q  := (Z.quot dd dv)%Z in
  let r  := (Z.rem  dd dv)%Z in
  let ov := (q <? wmin_signed sz)%Z || (q >? wmax_signed sz)%Z in

  if (dv == 0)%Z || ov then type_error else
  ok (flags_w2 (rflags_of_div) (:: (wrepr sz q) & (wrepr sz r))).

Definition x86_CQO sz (w:word sz) : exec (word sz) := 
  Let _ := check_size_16_64 sz in
  let r : word sz := (if msb w then -1 else 0)%R in
  ok r.

Definition add_carry sz (x y c: Z) : word sz :=
  wrepr sz (x + y + c).

Definition x86_ADC sz (v1 v2 : word sz) (c: bool) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let c := Z.b2z c in
  ok (rflags_of_aluop_w
    (add_carry sz (wunsigned v1) (wunsigned v2) c)
    (wunsigned v1 + wunsigned v2 + c)%Z
    (wsigned   v1 + wsigned   v2 + c)%Z).

Definition sub_borrow sz (x y c: Z) : word sz :=
  wrepr sz (x - y - c).

Definition x86_SBB sz (v1 v2 : word sz) (c:bool) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let c := Z.b2z c in
  ok ( rflags_of_aluop_w
    (sub_borrow sz (wunsigned v1) (wunsigned v2) c)
    (wunsigned v1 - (wunsigned v2 + c))%Z
    (wsigned   v1 - (wsigned   v2 + c))%Z).

Definition x86_NEG sz (w: word sz) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let vs := (- wsigned w)%Z in
  let v := (- w)%R in
  ok (flags_w
  ((:: Some (wsigned   v != vs), Some ((w != 0)%R), Some (SF_of_word v), Some (PF_of_word v) & Some (ZF_of_word v)) : sem_tuple b5_ty)
  v).

Definition x86_INC sz (w: word sz) : ex_tpl (b4w_ty sz) :=
  Let _  := check_size_8_64 sz in
  ok (rflags_of_aluop_nocf_w
    (w + 1)
    (wsigned w + 1)%Z).

Definition x86_DEC sz (w: word sz) : ex_tpl (b4w_ty sz) :=
  Let _  := check_size_8_64 sz in
  ok (rflags_of_aluop_nocf_w
    (w - 1)
    (wsigned w - 1)%Z).

Definition x86_SETcc (b:bool) : ex_tpl (w_ty U8) := ok (wrepr U8 (Z.b2z b)).

Definition x86_BT sz (x y: word sz) : ex_tpl (b_ty) :=
  Let _  := check_size_8_64 sz in
  ok (Some (wbit x y)).

Definition x86_LEA sz (disp base scale offset: word sz) : ex_tpl (w_ty sz) :=
  Let _  := check_size_32_64 sz in
  if check_scale (wunsigned scale) then
    ok ((disp + base + scale * offset)%R)
  else type_error.

Definition x86_TEST sz (x y: word sz) : ex_tpl  b5_ty :=
  Let _  := check_size_8_64 sz in
  ok (rflags_of_bwop (wand x y)).

Definition x86_CMP sz (x y: word sz) : ex_tpl b5_ty :=
  Let _  := check_size_8_64 sz in
  ok
    (rflags_of_aluop (x - y)
       (wunsigned x - wunsigned y)%Z (wsigned x - wsigned y)%Z).

Definition x86_AND sz (v1 v2: word sz) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  ok (rflags_of_bwop_w (wand v1 v2)).

Definition x86_ANDN sz (v1 v2: word sz) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_32_64 sz in
  let w := wandn v1 v2 in
  ok (flags_w (rflags_of_andn w) (w)).

Definition x86_OR sz (v1 v2: word sz) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  ok (rflags_of_bwop_w (wor v1 v2)).

Definition x86_XOR sz (v1 v2: word sz) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  ok (rflags_of_bwop_w (wxor v1 v2)).

Definition x86_NOT sz (v: word sz)  : ex_tpl (w_ty sz) :=
  Let _  := check_size_8_64 sz in
  ok (wnot v).

Definition x86_ROR sz (v: word sz) (i: u8) : ex_tpl (b2w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (:: None , None & v)
  else
    let r := wror v (wunsigned i) in
    let CF := msb r in
    let OF := if i == 1%R then Some (CF != msb v) else None in
    ok (:: OF , Some CF & r ).

Definition x86_ROL sz (v: word sz) (i: u8) : ex_tpl (b2w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (:: None , None & v)
  else
    let r := wrol v (wunsigned i) in
    let CF := lsb r in
    let OF := if i == 1%R then Some (msb r != CF) else None in
    ok (:: OF, Some CF & r ).

Definition rflags_OF {s} sz (i:word s) (r:word sz) rc OF : ex_tpl (b5w_ty sz) :=
    let OF := if i == 1%R then Some OF else None in
    let CF := Some rc in
    let SF := Some (SF_of_word r) in
    let PF := Some (PF_of_word r) in
    let ZF := Some (ZF_of_word r) in
    ok (:: OF, CF, SF, PF, ZF & r).

Definition x86_SHL sz (v: word sz) (i: u8) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (rflags_None_w v)
  else
    let rc := msb (wshl v (wunsigned i - 1)) in
    let r  := wshl v (wunsigned i) in
    rflags_OF i r rc (msb r (+) rc).

Definition x86_SHLD sz (v1 v2: word sz) (i: u8) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_16_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (rflags_None_w v1)
  else
    let rc := msb (wshl v1 (wunsigned i - 1)) in
    let r1 := wshl v1 (wunsigned i) in
    let r2 := wsar v2 (wsize_bits sz - (wunsigned i)) in
    let r  := wor r1 r2 in
    rflags_OF i r rc (msb r (+) rc).

Definition x86_SHR sz (v: word sz) (i: u8) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (rflags_None_w v)
  else
    let rc := lsb (wshr v (wunsigned i - 1)) in
    let r  := wshr v (wunsigned i) in
    rflags_OF i r rc (msb r).

Definition x86_SHRD sz (v1 v2: word sz) (i: u8) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_16_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (rflags_None_w v1)
  else
    let rc := lsb (wshr v1 (wunsigned i - 1)) in
    let r1 := wshr v1 (wunsigned i) in
    let r2 := wshl v2 (wsize_bits sz - (wunsigned i)) in
    let r  := wor r1 r2 in
    rflags_OF i r rc (msb r (+) msb v1).

Definition x86_SAR sz (v: word sz) (i: u8) : ex_tpl (b5w_ty sz) :=
  Let _ := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (rflags_None_w v)
  else
    let rc := lsb (wsar v (wunsigned i - 1)) in
    let r  := wsar v (wunsigned i) in
    rflags_OF i r rc false.

(* ---------------------------------------------------------------- *)
Definition x86_BSWAP sz (v: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_32_64 sz in
  ok (wbswap v).

(* ---------------------------------------------------------------- *)
Definition x86_MOVD sz (v: word sz) : ex_tpl (w_ty U128) :=
  Let _ := check_size_32_64 sz in
  ok (zero_extend U128 v).

(* ---------------------------------------------------------------- *)
Definition x86_VMOVDQU sz (v: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in ok v.

(* ---------------------------------------------------------------- *)
Definition x86_u128_binop sz (op: _ → _ → word sz) (v1 v2: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  ok (op v1 v2).

Definition x86_VPAND sz := x86_u128_binop (@wand sz).
Definition x86_VPANDN sz := x86_u128_binop (@wandn sz).
Definition x86_VPOR sz := x86_u128_binop (@wor sz).
Definition x86_VPXOR sz := x86_u128_binop (@wxor sz).

(* ---------------------------------------------------------------- *)
Definition x86_VPADD (ve: velem) sz := x86_u128_binop (lift2_vec ve +%R sz).
Definition x86_VPSUB (ve: velem) sz := 
  x86_u128_binop (lift2_vec ve (fun x y => x - y)%R sz).

Definition x86_VPMULL (ve: velem) sz v1 v2 := 
  Let _ := check_size_32_64 ve in
  x86_u128_binop (lift2_vec ve *%R sz) v1 v2.

Definition x86_VPMULU sz := x86_u128_binop (@wpmulu sz).

(* ---------------------------------------------------------------- *)
Definition x86_VPEXTR (ve: wsize) (v: u128) (i: u8) : ex_tpl (w_ty ve) :=
  (* This instruction is valid for smaller ve, but semantics is unusual,
      hence compiler correctness would not be provable. *)
  Let _ := check_size_32_64 ve in
  ok (nth (0%R: word ve) (split_vec ve v) (Z.to_nat (wunsigned i))).

(* ---------------------------------------------------------------- *)
Definition x86_VPINSR (ve: velem) (v1: u128) (v2: word ve) (i: u8) : ex_tpl (w_ty U128) :=
  ok (wpinsr v1 v2 i).

Arguments x86_VPINSR : clear implicits.

(* ---------------------------------------------------------------- *)
Definition x86_u128_shift sz' sz (op: word sz' → Z → word sz')
  (v: word sz) (c: u8) : ex_tpl (w_ty sz) :=
  Let _ := check_size_16_64 sz' in
  Let _ := check_size_128_256 sz in
  ok (lift1_vec sz' (λ v, op v (wunsigned c)) sz v).

Arguments x86_u128_shift : clear implicits.

Definition x86_VPSLL (ve: velem) sz := x86_u128_shift ve sz (@wshl _).
Definition x86_VPSRL (ve: velem) sz := x86_u128_shift ve sz (@wshr _).
Definition x86_VPSRA (ve: velem) sz := x86_u128_shift ve sz (@wsar _).

(* ---------------------------------------------------------------- *)
Definition x86_u128_shift_variable ve sz op v1 v2 : ex_tpl (w_ty sz) :=
  Let _ := check_size_32_64 ve in
  Let _ := check_size_128_256 sz in
  ok (lift2_vec ve (λ v1 v2, op v1 (wunsigned v2)) sz v1 v2).

Arguments x86_u128_shift_variable : clear implicits.

Definition x86_VPSLLV ve sz := x86_u128_shift_variable ve sz (@wshl _).
Definition x86_VPSRLV ve sz := x86_u128_shift_variable ve sz (@wshr _).

(* ---------------------------------------------------------------- *)
Definition x86_vpsxldq sz op (v1: word sz) (v2: u8) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  ok (op v1 v2).

Definition x86_VPSLLDQ sz := x86_vpsxldq (@wpslldq sz).
Definition x86_VPSRLDQ sz := x86_vpsxldq (@wpsrldq sz).

(* ---------------------------------------------------------------- *)
Definition x86_VPSHUFB sz := x86_u128_binop (@wpshufb sz).

(* ---------------------------------------------------------------- *)
Definition x86_vpshuf sz (op: word sz → Z → word sz) (v1: word sz) (v2: u8) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  ok (op v1 (wunsigned v2)).

Arguments x86_vpshuf : clear implicits.

Definition x86_VPSHUFHW sz := x86_vpshuf sz (@wpshufhw _).
Definition x86_VPSHUFLW sz := x86_vpshuf sz (@wpshuflw _).
Definition x86_VPSHUFD sz := x86_vpshuf sz (@wpshufd _).

(* ---------------------------------------------------------------- *)
Definition x86_VPUNPCKH ve sz := x86_u128_binop (@wpunpckh sz ve).
Definition x86_VPUNPCKL ve sz := x86_u128_binop (@wpunpckl sz ve).

(* ---------------------------------------------------------------- *)
Definition x86_VPBLENDD sz (v1 v2: word sz) (m: u8) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  ok (wpblendd v1 v2 m).

(* ---------------------------------------------------------------- *)
Definition x86_VPBROADCAST ve sz (v: word ve) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  ok (wpbroadcast sz v).

(* ---------------------------------------------------------------- *)
Definition x86_VEXTRACTI128 (v: u256) (i: u8) : ex_tpl (w_ty U128) :=
  let r := if lsb i then wshr v U128 else v in
  ok (zero_extend U128 r).

Definition x86_VINSERTI128 (v1: u256) (v2: u128) (m: u8) : ex_tpl (w_ty U256) :=
  ok (winserti128 v1 v2 m).

(* ---------------------------------------------------------------- *)
Definition x86_VPERM2I128 (v1 v2: u256) (m: u8) : ex_tpl (w_ty U256) :=
  ok (wperm2i128 v1 v2 m).

Definition x86_VPERMQ (v: u256) (m: u8) : ex_tpl (w_ty U256) :=
  ok (wpermq v m).


Definition Ox86_MOV_instr               := mk_instr_w_w "Ox86_MOV" x86_MOV.
Definition Ox86_MOVSX_instr             := mk_instr_w_w' "Ox86_MOVSX" x86_MOVSX.
Definition Ox86_MOVZX_instr             := mk_instr_w_w' "Ox86_MOVZX" x86_MOVZX.
Definition Ox86_MOVZX32_instr           := mk_instr (pp_s "Ox86_MOVZX32") w32_ty w64_ty (λ x : u32, ok (zero_extend U64 x)) U32.
Definition Ox86_ADD_instr               := mk_instr_w2_b5w "Ox86_ADD" x86_ADD.
Definition Ox86_SUB_instr               := mk_instr_w2_b5w "Ox86_SUB" x86_SUB.
Definition Ox86_CMOVcc_instr            := mk_instr_bw2_w "Ox86_CMOVcc" x86_CMOVcc.
Definition Ox86_MUL_instr               := mk_instr_w2_b5w2 "Ox86_MUL" x86_MUL.
Definition Ox86_IMUL_instr              := mk_instr_w2_b5w2 "Ox86_IMUL" x86_IMUL.
Definition Ox86_IMULt_instr             := mk_instr_w2_b5w "Ox86_IMULt" x86_IMULt.
Definition Ox86_IMULtimm_instr          := mk_instr_w2_b5w "Ox86_IMULtimm" x86_IMULt. (* /!\ same as above *)
Definition Ox86_DIV_instr               := mk_instr_w3_b5w2 "Ox86_DIV" x86_DIV.
Definition Ox86_IDIV_instr              := mk_instr_w3_b5w2 "Ox86_IDIV" x86_IDIV.
Definition Ox86_CQO_instr               := mk_instr_w_w "Ox86_CQO" x86_CQO.
Definition Ox86_ADC_instr               := mk_instr_w2b_b5w "Ox86_ADC" x86_ADC.
Definition Ox86_SBB_instr               := mk_instr_w2b_b5w "Ox86_SBB" x86_SBB.
Definition Ox86_NEG_instr               := mk_instr_w_b5w "Ox86_NEG" x86_NEG.
Definition Ox86_INC_instr               := mk_instr_w_b4w "Ox86_INC" x86_INC.
Definition Ox86_DEC_instr               := mk_instr_w_b4w "Ox86_DEC" x86_DEC.
Definition Ox86_SETcc_instr             := mk_instr (pp_s "Ox86_SETcc") b_ty w8_ty x86_SETcc U8.
Definition Ox86_BT_instr                := mk_instr_w2_b "Ox86_BT" x86_BT.
Definition Ox86_LEA_instr               := mk_instr_w4_w "Ox86_LEA" x86_LEA.
Definition Ox86_TEST_instr              := mk_instr_w2_b5 "Ox86_TEST" x86_TEST.
Definition Ox86_CMP_instr               := mk_instr_w2_b5 "Ox86_CMP" x86_CMP.
Definition Ox86_AND_instr               := mk_instr_w2_b5w "Ox86_AND" x86_AND.
Definition Ox86_ANDN_instr              := mk_instr_w2_b5w "Ox86_ANDN" x86_ANDN.
Definition Ox86_OR_instr                := mk_instr_w2_b5w "Ox86_OR" x86_OR.
Definition Ox86_XOR_instr               := mk_instr_w2_b5w "Ox86_XOR" x86_XOR.
Definition Ox86_NOT_instr               := mk_instr_w_w "Ox86_NOT" x86_NOT.
Definition Ox86_ROR_instr               := mk_instr_ww8_b2w "Ox86_ROR" x86_ROR.
Definition Ox86_ROL_instr               := mk_instr_ww8_b2w "Ox86_ROL" x86_ROL.
Definition Ox86_SHL_instr               := mk_instr_ww8_b5w "Ox86_SHL" x86_SHL.
Definition Ox86_SHR_instr               := mk_instr_ww8_b5w "Ox86_SHR" x86_SHR.
Definition Ox86_SAR_instr               := mk_instr_ww8_b5w "Ox86_SAR" x86_SAR.
Definition Ox86_SHLD_instr              := mk_instr_w2w8_b5w "Ox86_SHLD" x86_SHLD.
Definition Ox86_SHRD_instr              := mk_instr_w2w8_b5w "Ox86_SHRD" x86_SHRD.
Definition Ox86_BSWAP_instr             := mk_instr_w_w "Ox86_BSWAP" x86_BSWAP.
Definition Ox86_MOVD_instr              := mk_instr_w_w128 "Ox86_MOVD" x86_MOVD.
Definition Ox86_VMOVDQU_instr           := mk_instr_w_w "Ox86_VMOVDQU" x86_VMOVDQU.
Definition Ox86_VPAND_instr             := mk_instr_w2_w "Ox86_VPAND" x86_VPAND.
Definition Ox86_VPANDN_instr            := mk_instr_w2_w "Ox86_VPANDN" x86_VPANDN.
Definition Ox86_VPOR_instr              := mk_instr_w2_w "Ox86_VPOR" x86_VPOR.
Definition Ox86_VPXOR_instr             := mk_instr_w2_w "Ox86_VPXOR" x86_VPXOR.
Definition Ox86_VPADD_instr             := mk_ve_instr_w2_w "Ox86_VPADD" x86_VPADD.
Definition Ox86_VPSUB_instr             := mk_ve_instr_w2_w "Ox86_VPSUB" x86_VPSUB.
Definition Ox86_VPMULL_instr            := mk_ve_instr_w2_w "Ox86_VPMULL" x86_VPMULL.
Definition Ox86_VPMULU_instr sz         := mk_instr (pp_s "Ox86_VPMULU") (w2_ty sz sz) (w_ty sz) (@x86_VPMULU sz) sz.

(* 128 *)
Definition Ox86_VPEXTR_instr ve         := mk_instr (pp_sz "Ox86_VPEXTR" ve) w128w8_ty       (w_ty ve) (x86_VPEXTR ve) U128.
Definition Ox86_VPINSR_instr ve         := mk_instr (pp_ve "Ox86_VPINSR" ve) (w128ww8_ty ve) w128_ty (x86_VPINSR ve) U128.

Definition Ox86_VPSLL_instr             := mk_ve_instr_ww8_w "Ox86_VPSLL" x86_VPSLL.
Definition Ox86_VPSRL_instr             := mk_ve_instr_ww8_w "Ox86_VPSRL" x86_VPSRL.
Definition Ox86_VPSRA_instr             := mk_ve_instr_ww8_w "Ox86_VPSRA" x86_VPSRA.
Definition Ox86_VPSLLV_instr            := mk_ve_instr_w2_w "Ox86_VPSLLV" x86_VPSLLV.
Definition Ox86_VPSRLV_instr            := mk_ve_instr_w2_w "Ox86_VPSRLV" x86_VPSRLV.
Definition Ox86_VPSLLDQ_instr           := mk_instr_ww8_w "Ox86_VPSLLDQ" x86_VPSLLDQ.
Definition Ox86_VPSRLDQ_instr           := mk_instr_ww8_w "Ox86_VPSRLDQ" x86_VPSRLDQ.
Definition Ox86_VPSHUFB_instr           := mk_instr_w2_w "Ox86_VPSHUFB" x86_VPSHUFB.
Definition Ox86_VPSHUFHW_instr          := mk_instr_ww8_w "Ox86_VPSHUFHW" x86_VPSHUFHW.
Definition Ox86_VPSHUFLW_instr          := mk_instr_ww8_w "Ox86_VPSHUFLW" x86_VPSHUFLW.
Definition Ox86_VPSHUFD_instr           := mk_instr_ww8_w "Ox86_VPSHUFD" x86_VPSHUFD.
Definition Ox86_VPUNPCKH_instr          := mk_ve_instr_w2_w "Ox86_VPUNPCKH" x86_VPUNPCKH.
Definition Ox86_VPUNPCKL_instr          := mk_ve_instr_w2_w "Ox86_VPUNPCKL" x86_VPUNPCKL.
Definition Ox86_VPBLENDD_instr          := mk_instr_w2w8_w "Ox86_VPBLENDD" x86_VPBLENDD.
Definition Ox86_VPBROADCAST_instr       := mk_ve_instr_w_w "Ox86_VPBROADCAST" x86_VPBROADCAST.


(* 256 *)
Definition Ox86_VBROADCASTI128_instr    := mk_instr (pp_s "Ox86_VBROADCASTI128")  w128_ty       w256_ty (x86_VPBROADCAST U256) U256.
Definition Ox86_VEXTRACTI128_instr      := mk_instr (pp_s "Ox86_VEXTRACTI128")    w256w8_ty     w128_ty x86_VEXTRACTI128 U256.
Definition Ox86_VINSERTI128_instr       := mk_instr (pp_s "Ox86_VINSERTI128")     w256w128w8_ty w256_ty x86_VINSERTI128 U256.
Definition Ox86_VPERM2I128_instr        := mk_instr (pp_s "Ox86_VPERM2I128")      w256x2w8_ty   w256_ty x86_VPERM2I128 U256.
Definition Ox86_VPERMQ_instr            := mk_instr (pp_s "Ox86_VPERMQ")          w256w8_ty     w256_ty x86_VPERMQ U256.

Definition get_x86_instr o : Instruction :=
  match o with
  | Ox86_MOV sz             => Ox86_MOV_instr sz
  | Ox86_MOVSX sz sz'       => Ox86_MOVSX_instr sz sz'
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
  | Ox86_VPEXTR ve          => Ox86_VPEXTR_instr ve
  end.


Scheme Equality for x86_instr_t.
Lemma x86_instr_t_eq_axiom : Equality.axiom x86_instr_t_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_x86_instr_t_dec_bl.
  by apply: internal_x86_instr_t_dec_lb.
Qed.

Definition x86_instr_t_eqMixin     := Equality.Mixin x86_instr_t_eq_axiom.
Canonical  x86_instr_t_eqType      := Eval hnf in EqType x86_instr_t x86_instr_t_eqMixin.
