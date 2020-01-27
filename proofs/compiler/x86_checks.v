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
Require Import wsize word.
Import Utf8 Relation_Operators.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import x86_decl.

(* ---------------------------------------------------------------- *)
(* DEFINE CHECKS *)

Definition fake_check (_:list asm_arg) : bool := true.
Definition fake_check_sz (sz:wsize) (_:list asm_arg) : bool := true.
Definition fake_check_sz_sz' (sz sz':wsize) (_:list asm_arg) : bool := true.

(* ---------------------------------------------------------------- *)
Module Checks.

Definition none (_:list asm_arg) : bool := true.
Definition none_sz (sz:wsize) (_:list asm_arg) : bool := true.

(* ---------------------------------------------------------------- *)

(* Recursively apply checks *)

(* One operand *)
Fixpoint rec_1 (sz: wsize) (lf : list (wsize -> asm_arg -> bool)) (a: asm_arg) :=
  match lf with
  | [::]    => false
  | f :: lf => if (f sz a) then true else rec_1 sz lf a
  end.

Definition apply_1 (sz: wsize) (f: list (wsize -> asm_arg -> bool)) (args: list asm_arg) : bool :=
  match args with
  | [:: a ] => rec_1 sz f a
  | _       => false
  end.

(* Two operands *)
Fixpoint rec_2 (sz: wsize) (lf : list (wsize -> asm_arg -> asm_arg -> bool)) (a b: asm_arg) :=
  match lf with
  | [::]    => false
  | f :: lf => if (f sz a b) then true else rec_2 sz lf a b
  end.

Definition apply_2 (sz: wsize) (f: list (wsize -> asm_arg -> asm_arg -> bool)) (args: list asm_arg) : bool :=
  match args with
  | [:: a ; b] => rec_2 sz f a b
  | _          => false
  end.

Fixpoint rec_2' (szi szo: wsize) (lf : list (wsize -> wsize -> asm_arg -> asm_arg -> bool)) (a b: asm_arg) :=
  match lf with
  | [::]    => false
  | f :: lf => if (f szi szo a b) then true else rec_2' szi szo lf a b
  end.

Definition apply_2' (szi szo: wsize) (f: list (wsize -> wsize -> asm_arg -> asm_arg -> bool)) (args: list asm_arg) : bool :=
  match args with
  | [:: a ; b] => rec_2' szi szo f a b
  | _          => false
  end.

(* Three operands *)
Fixpoint rec_3 (sz: wsize) (lf : list (wsize -> asm_arg -> asm_arg -> asm_arg -> bool)) (a b c: asm_arg) :=
  match lf with
  | [::]    => false
  | f :: lf => if (f sz a b c) == true then true else rec_3 sz lf a b c
  end.

Definition apply_3 (sz: wsize) (f: list (wsize -> asm_arg -> asm_arg -> asm_arg -> bool)) (args: list asm_arg) : bool :=
  match args with
  | [:: a ; b ; c] => rec_3 sz f a b c
  | _              => false
  end.

(* Four operands *)
Fixpoint rec_4 (sz: wsize) (lf : list (wsize -> asm_arg -> asm_arg -> asm_arg -> asm_arg -> bool)) (a b c d: asm_arg) :=
  match lf with
  | [::]    => false
  | f :: lf => if (f sz a b c d) == true then true else rec_4 sz lf a b c d
  end.

Definition apply_4 (sz: wsize) (f: list (wsize -> asm_arg -> asm_arg -> asm_arg -> asm_arg -> bool)) (args: list asm_arg) : bool :=
  match args with
  | [:: a ; b ; c ; d] => rec_4 sz f a b c d
  | _              => false
  end.

(* ---------------------------------------------------------------- *)

Definition near_eq sz sz' := if sz == U64 then sz' == U32 else sz == sz'.

(* ---------------------------------------------------------------- *)

Definition rm (sz:wsize) a :=
  match a with
  | Reg _ => true
  | Adr _ => true
  | _ => false
  end.

Definition rm_eq8 (sz:wsize) a :=
  match a with
  | Reg _ => (sz == U8)
  | Adr _ => (sz == U8)
  | _ => false
  end.

Definition r_16 (sz:wsize) a :=
  match a with
  | Reg _ => (sz > U16)
  | _ => false
  end.

(* ---------------------------------------------------------------- *)

Definition rm_r (sz:wsize) a b :=
  match a, b with
  | Reg _, Reg _ => true
  | Adr _, Reg _ => true
  (* dest cannot be glob *)
  | _, _ => false
  end.

Definition r_rm (sz:wsize) a b :=
  match a, b with
  | Reg _, Adr _ => true
  | Reg _, Reg _ => true
  | Reg _, Glob _ => true
  | _, _ => false
  end.

Definition r_m (sz:wsize) a b := 
  match a, b with
  | Reg _, Adr _ => true
  | _, _ => false
  end.
 
Definition r_imm_eq (sz: wsize) a b :=
  match a, b with
  | Reg _ , Imm sz' _ => (sz == sz')
  | _, _ => false
  end.

Definition rm_imm_near_eq (sz: wsize) a b :=
  match a, b with
  | Reg _, Imm sz' _ => near_eq sz sz'
  | Adr _, Imm sz' _ => near_eq sz sz'
  | _, _ => false
  end.

Definition r_r_rm (sz:wsize) a b c := 
  match a, b, c with
  | Reg _, Reg _, Reg _ => true
  | Reg _, Reg _, Adr _ => true
  | Reg _, Reg _, Glob _ => true
  | _, _, _ => false
  end.
 
Definition rm_imm8 (sz: wsize) a b :=
  match a, b with
  | Reg _, Imm U8 _ => true
  | Adr _, Imm U8 _ => true
  | Glob _, Imm U8 _ => true (* need to be checked *)
  | _, _ => false
  end.

Definition rm_imm_8 (sz: wsize) a b :=
  match a, b with
  | Reg _, Imm U8 _ => (sz > U8)
  | Adr _, Imm U8 _ => (sz > U8)
  | Glob _, Imm U8 _ => (sz > U8) (* need to be checked *)
  | _, _ => false
  end.

Definition r_rm_8 (sz : wsize) a b :=
  match a, b with
  | Reg _, Reg _ => (sz > U8)
  | Reg _, Adr _ => (sz > U8)
  | Reg _, Glob _ => (sz > U8)
  | _ , _ => false
  end.

Definition rm_r_8 (sz:wsize) a b :=
  match a, b with
  | Adr _, Reg _ => (sz > U8)
  | Reg _, Reg _ => (sz > U8)
  | Glob _, Reg _ => (sz > U8) (* need to be checked *)
  | _, _ => false
  end.

Definition r_rm_8_8 (sz sz': wsize) a b :=
  match a, b with
  | Reg _, Adr _ => (sz > U8) && (sz' == U8)
  | Reg _, Reg _ => (sz > U8) && (sz' == U8)
  | Reg _, Glob _ => (sz > U8) && (sz' == U8)
  | _ , _ => false
  end.

Definition r_rm_16 (sz : wsize) a b :=
  match a, b with
  | Reg _, Reg _ => (sz > U16)
  | Reg _, Adr _ => (sz > U16)
  | Reg _, Glob _ => (sz > U16)
  | _ , _ => false
  end.

Definition r_rm_16_16 (sz sz': wsize) a b :=
  match a, b with
  | Reg _, Reg _ => (sz > U16) && (sz' == U16)
  | Reg _, Adr _ => (sz > U16) && (sz' == U16)
  | Reg _, Glob _ => (sz > U16) && (sz' == U16)
  | _ , _ => false
  end.

Definition xmm_rm_16 (sz: wsize) a b :=
  match a, b with
  | XMM _, Reg _ => (sz > U16)
  | XMM _, Adr _ => (sz > U16)
  | XMM _, Glob _ => (sz > U16)
  | _ , _ => false
  end.

Definition xmm_r_16 (sz: wsize) a b :=
  match a, b with
  | XMM _, Reg _ => (sz > U16)
  | _ , _ => false
  end.

Definition rm_xmm_16 (sz: wsize) a b :=
  match a, b with
  | Reg _, XMM _ => (sz > U16)
  | Adr _, XMM _ => (sz > U16)
  | Glob _, XMM _ => (sz > U16)
  | _ , _ => false
  end.

Definition xmm_xmm (sz: wsize) a b :=
  match a, b with
  | XMM _, XMM _ => true
  | _ , _ => false
  end.

Definition xmm_xmmm (sz : wsize) a b :=
  match a, b with
  | XMM _, XMM _ => true 
  | XMM _, Adr _ => true 
  | _, _ => false
  end.

Definition xmmm_xmm (sz : wsize) a b :=
  match b, a with
  | XMM _, XMM _ => true 
  | XMM _, Adr _ => true 
  | _, _ => false
  end.

(* ----------------------------------- *)

Definition r_rm_imm8_8 (sz : wsize) a b c :=
  match a, b, c with
  | Reg _, Reg _, Imm U8 _ => true 
  | Reg _, Adr _, Imm U8 _ => true 
  | Reg _, Glob _, Imm U8 _ => true 
  | _ , _, _ => false
  end.

Definition r_rm_imm_8_eq (sz : wsize) a b c :=
  match a, b, c with
  | Reg _, Reg _, Imm sz' _ => near_eq sz sz'
  | Reg _, Adr _, Imm sz' _ => near_eq sz sz' 
  | Reg _, Glob _, Imm sz' _ => near_eq sz sz' 
  | _ , _, _ => false
  end.

Definition rm_r_imm8_8 (sz : wsize) a b c :=
  match a, b, c with
  | Reg _, Reg _, Imm U8 _ => (sz > U8)
  | Adr _, Reg _, Imm U8 _ => (sz > U8)
  (* dest cannot be Glob *)
  | _ , _, _ => false
  end.

Definition r_V_rm_16 (sz : wsize) (a b c: asm_arg) :=
  match a, b, c with
  | Reg _, _, Reg _ => (sz > U16)
  | Reg _, _, Adr _ => (sz > U16)
  | Reg _, _, Glob _ => (sz > U16)
  | _, _, _ => false
  end.


Definition xmm_xmm_xmm (sz: wsize) a b c :=
  match a, b, c with
  | XMM _, XMM _, XMM _ => true
  | _, _, _ => false
  end.

Definition xmm_xmm_imm8 (sz: wsize) a b c :=
  match a, b, c with
  | XMM _, XMM _, Imm U8 _ => true
  | _, _, _ => false
  end.

Definition rm_xmm_imm8_eq8 (sz : wsize) a b c :=
  match a, b, c with
  | Reg _, XMM _, Imm U8 _ => (sz == U8)
  | Adr _, XMM _, Imm U8 _ => (sz == U8)
  (* dest cannot be Glob *)
  | _, _, _ => false
  end.

Definition rm_xmm_imm8_16 (sz : wsize) a b c :=
  match a, b, c with
  | Reg _, XMM _, Imm U8 _ => (sz > U16)
  | Adr _, XMM _, Imm U8 _ => (sz > U16)
  (* dest cannot be Glob *)
  | _, _, _ => false
  end.

(* ----------------------------------- *)

Definition xmm_xmm_rm_imm8_16 (sz : wsize) a b c d :=
  match a, b, c, d with
  | XMM _, XMM _, Reg _, Imm U8 _ => (sz > U16)
  | XMM _, XMM _, Adr _, Imm U8 _ => (sz > U16)
  (* dest cannot be Glob *)
  | _, _, _, _ => false
  end.

Definition xmm_xmm_xmm_imm8 (sz : wsize) a b c d :=
  match a, b, c, d with
  | XMM _, XMM _, XMM _, Imm U8 _ => true
  | _, _, _, _ => false
  end.

Definition xmm_xmm_xmmm (sz : wsize) a b c :=
  match a, b, c with
  | XMM _, XMM _, XMM _ => true 
  | XMM _, XMM _, Adr _ => true 
  | _, _, _ => false
  end.

(* ---------------------------------------------------------------- *)


Definition mov sz (args: list asm_arg) :=
apply_2 sz [:: rm_r ; r_rm ; r_imm_eq ; rm_imm_near_eq ] args.

Definition lea sz (args: list asm_arg) :=
apply_2 sz [:: r_m ] args.

Definition movsx_movzx sz sz' (args: list asm_arg) :=
apply_2' sz sz' [:: r_rm_8_8; r_rm_16_16 ] args.

Definition cmovcc sz (args:list asm_arg) :=
apply_2 sz [:: r_rm_8 ] args.

Definition add_sub_adc_sbb sz (args: list asm_arg) :=
apply_2 sz [:: rm_imm_near_eq; rm_imm_8 ; rm_r ; r_rm ] args.

Definition adcx sz (args: list asm_arg) := 
apply_2 sz [:: r_rm] args.

Definition mulx sz (args: list asm_arg) := 
apply_3 sz [:: r_r_rm] args.
  
Definition neg_inc_dec_not sz (args: list asm_arg) :=
apply_1 sz [:: rm ] args.

Definition mul_div sz (args:list asm_arg) :=
apply_1 sz [:: rm ] args.

Definition multr sz (args: list asm_arg) :=
apply_2 sz [:: r_rm_16 ] args.

Definition multri sz (args: list asm_arg) :=
apply_3 sz [:: r_rm_imm8_8 ; r_rm_imm_8_eq ] args.

Definition setcc (args: list asm_arg) :=
apply_1 U8 [:: rm_eq8 ] args.

Definition bt sz (args: list asm_arg) :=
apply_2 sz [:: rm_r_8 ; rm_imm_8 ] args.

Definition test sz (args: list asm_arg) :=
apply_2 sz [:: rm_imm_near_eq ; rm_r ] args.

Definition cmp_and_or_xor sz (args: list asm_arg) :=
apply_2 sz [:: rm_imm_near_eq ; rm_imm_8 ; rm_r ; r_rm ] args.

(* TODO: PLEASE CHECK, this one is weird. *)
Definition andn sz (args: list asm_arg) :=
apply_3 sz [:: r_V_rm_16 ] args.

Definition ror_rol_shr_shl_sal_sar sz (args: list asm_arg) :=
apply_2 sz [:: rm_imm8; rm_r ] args.

Definition shld_shrd sz (args: list asm_arg) :=
apply_3 sz [:: rm_r_imm8_8 ] args.

Definition bswap sz (args: list asm_arg) :=
apply_1 sz [:: r_16 ] args.

Definition movd_movq sz (args: list asm_arg) :=
apply_2 sz [:: xmm_rm_16 ; rm_xmm_16 ] args. (* but it looks like our definition of movd is only [movd xmm rm] *)

Definition vmovdqu sz (args: list asm_arg) :=
apply_2 sz [:: xmm_xmmm; xmmm_xmm ] args.

Definition xmm_xmm_xmm_ sz (args: list asm_arg) :=
apply_3 sz [:: xmm_xmm_xmm ] args.

Definition xmm_xmm_xmmm_ sz (args: list asm_arg) :=
apply_3 sz [:: xmm_xmm_xmmm ] args.

Definition xmm_xmm_imm8_ sz (args: list asm_arg) :=
apply_3 sz [:: xmm_xmm_imm8 ] args.

Definition vpextr sz (args: list asm_arg) :=
apply_3 sz [:: rm_xmm_imm8_eq8 ; rm_xmm_imm8_16 ] args.

Definition xmm_xmm_rm_imm8_16_ sz (args: list asm_arg) :=
apply_4 sz [:: xmm_xmm_rm_imm8_16 ] args.

Definition xmm_xmm_xmm_imm8_ sz (args: list asm_arg) :=
apply_4 sz [:: xmm_xmm_xmm_imm8 ] args.

Definition vpbroadcast sz (args: list asm_arg) :=
apply_2 sz [:: xmm_r_16 ; xmm_xmm ] args.
(* VPBROADCASTB/W/D/Q—Load with Broadcast Integer Data from General Purpose Register *)
(* xmm_r_16 ;  *)
(* VPBROADCAST—Load Integer and Broadcast *)
(* xmm_xmm *)

End Checks.