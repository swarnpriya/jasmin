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

(* ** Machine word *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith utils type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)

Module Type WSIZE.
  Parameter wordsize : nat.
  Parameter wordsize_not_zero : wordsize <> 0%nat.
  Parameter x86_shift_zmask : Z.
  Parameter x86_rotate_mod  : Z.
End WSIZE.

Module Wordsize_8.
  Definition wordsize : nat := 8.
  Lemma wordsize_not_zero : wordsize <> 0%nat.
  Proof. done. Qed.
  Definition x86_shift_zmask := 31.
  Definition x86_rotate_mod  := 9.
End Wordsize_8.

Module Wordsize_16.
  Definition wordsize : nat := 16.
  Lemma wordsize_not_zero : wordsize <> 0%nat.
  Proof. done. Qed.
  Definition x86_shift_zmask := 31.
  Definition x86_rotate_mod  := 17.
End Wordsize_16.

Module Wordsize_32.
  Definition wordsize : nat := 32.
  Lemma wordsize_not_zero : wordsize <> 0%nat.
  Proof. done. Qed.
  Definition x86_shift_zmask := 31.
  Definition x86_rotate_mod  := 32.
End Wordsize_32.

Module Wordsize_64.
  Definition wordsize : nat := 64.
  Lemma wordsize_not_zero : wordsize <> 0%nat.
  Proof. done. Qed.
  Definition x86_shift_zmask := 63.
  Definition x86_rotate_mod  := 64.
End Wordsize_64.

(* None => undef *)
Record rflags2 := MkFlag2 {
   f2_OF : option bool; 
   f2_CF : option bool;
}.

Record rflags4 := MkFlag4 {
   f4_OF : option bool; 
   f4_SF : option bool;
   f4_PF : option bool;
   f4_ZF : option bool;
}.

Record rflags5 := MkFlag5 {
   f5_OF : option bool; 
   f5_CF : option bool;
   f5_SF : option bool;
   f5_PF : option bool;
   f5_ZF : option bool;                   
}.

Definition flag (b:bool) := Some b.
Definition ftrue  := flag true.
Definition ffalse := flag false.
Definition fundef : option bool := None.

Definition Zofb (b:bool) : Z := if b then 1 else 0.

Notation iword := Z (only parsing).

Create HintDb Iword discriminated.

Module MakeI (WS:WSIZE).

  Include (Integers.Make WS).

  Definition weq (w1 w2: int) := unsigned w1 == unsigned w2.

  Definition wneq (w1 w2: int) := ~~ (unsigned w1 == unsigned w2).

  Definition wcmp (w1 w2:int) := 
    Z.compare (unsigned w1) (unsigned w2).

  Coercion unsigned : int >-> Z.

  Module Theory.
  
  Lemma w_eqP : Equality.axiom weq.
  Proof.
    move=> p1 p2;rewrite /weq.
    have := eq_spec p1 p2;rewrite /eq /Coqlib.zeq.
    by case:Z.eq_dec => [/eqP | /eqP /negbTE] ->;constructor.
  Qed.

  Definition w_eqMixin := EqMixin w_eqP.
  Canonical w_eqType  := EqType int w_eqMixin.

  Lemma ueqP n1 n2: reflect (n1 = n2) (unsigned n1 == unsigned n2).
  Proof. by apply (n1 =P n2). Qed.

  Instance i64O : Cmp wcmp.
  Proof.
    rewrite /wcmp;constructor.
    + by move=> ??;rewrite Z.compare_antisym. 
    + move=> ????;case:Z.compare_spec=> [->|H1|H1];
       case:Z.compare_spec=> H2 //= -[] <- //;
       rewrite -?H2 ?Z.compare_gt_iff ?Z.compare_lt_iff //.
      + move: (H2);rewrite -?Z.compare_lt_iff => ->.
        by rewrite Z.compare_lt_iff;apply: Z.lt_trans H1 H2. 
      by apply: Z.lt_trans H2 H1. 
    by move=> x y /Z.compare_eq Heq; rewrite -(repr_unsigned x) -(repr_unsigned y) Heq.
  Qed.

  End Theory.
  Export Theory.

  Definition b_to_w (b:bool) := if b then one else zero.

  Definition waddc (x y:int) (c:bool) :=
    let n := unsigned x + unsigned y + unsigned (b_to_w c) in
    (modulus <=? n, repr n).

  Definition wsubc (x y:int) (c:bool) :=
    let n := unsigned x - (unsigned y + unsigned (b_to_w c)) in
    (n <? 0, repr n).

  Definition wmulu (x y: int) := 
    let n := unsigned x * unsigned y in
    (repr (Z.quot n modulus), repr n).
 
  Definition wmuls (x y: int) := 
    let n := signed x * signed y in
    (repr (Z.quot n modulus), repr n).
  
  Definition wsle (x y:int) := signed x <=? signed y.
  Definition wslt (x y:int) := signed x <?  signed y.

  Definition wule (x y:int) := unsigned x <=? unsigned y.
  Definition wult (x y:int) := unsigned x <?  unsigned y.

  Definition wsge (x y:int) := wsle y x.
  Definition wsgt (x y:int) := wslt y x.

  Definition wuge (x y:int) := wule y x.
  Definition wugt (x y:int) := wult y x.

  Lemma lt_unsigned x: (modulus <=? unsigned x)%Z = false.
  Proof. by rewrite Z.leb_gt;case: (unsigned_range x). Qed.

  Lemma le_unsigned x: (0 <=? unsigned x)%Z = true.
  Proof. by rewrite Z.leb_le;case: (unsigned_range x). Qed.

  Lemma wsle_refl x : wsle x x.
  Proof. by rewrite /wsle Z.leb_refl. Qed.

  Lemma wule_refl x : wule x x.
  Proof. by rewrite /wule Z.leb_refl. Qed.

  Lemma wslt_irrefl x : wslt x x = false.
  Proof. by rewrite /wslt Z.ltb_irrefl. Qed.

  Lemma wult_irrefl x : wult x x = false.
  Proof. by rewrite /wult Z.ltb_irrefl. Qed.

  Definition sem_lsr (v i:int) :=
    let i := and i (repr WS.x86_shift_zmask) in
    if i == zero then v else shru v i.

  Definition sem_lsl (v i:int) :=
    let i := and i (repr WS.x86_shift_zmask) in
    if i == zero then v else shl v i.

  Definition sem_asr (v i:int) :=
    let i := and i (repr WS.x86_shift_zmask) in
    if i == zero then v else shr v i.

  Definition msb (w : int) := (signed w <? 0)%Z.
  Definition lsb (w : int) := (and w one) != zero.

  Definition dwordu (hi lo : int) :=
    (unsigned hi * modulus + unsigned lo)%Z.

  Definition dwords (hi lo : int) :=
    (signed hi * modulus + unsigned lo)%Z.

  Definition wordbit (w : int) (i : nat) :=
    and (shr w (repr (Z.of_nat i))) one != zero.

  Definition word2bits (w : int) : seq bool :=
    [seq wordbit w i | i <- iota 0 wordsize].

  Definition SF_of_word (w : int) :=
    flag (msb w).

  Definition PF_of_word (w : int) :=
    flag (lsb w).

  Definition ZF_of_word (w : int) :=
    flag (eq w zero).

  (* -------------------------------------------------------------------- *)
  Definition rflags_of_bwop (w : int) :=
    {| f5_OF := ffalse; 
       f5_CF := ffalse; 
       f5_SF := SF_of_word w; 
       f5_PF := PF_of_word w; 
       f5_ZF := ZF_of_word w |}.

  (* -------------------------------------------------------------------- *)
  Definition rflags_of_aluop (w : int) (vu vs : Z) :=
    {| f5_OF := flag (unsigned w != vs); 
       f5_CF := flag (unsigned w != vu);
       f5_SF := SF_of_word w; 
       f5_PF := PF_of_word w; 
       f5_ZF := ZF_of_word w |}.

  (* -------------------------------------------------------------------- *)
  Definition rflags_of_mul (ov : bool) :=
    {| f5_OF := flag ov;  
       f5_CF := flag ov;
       f5_SF := fundef; 
       f5_PF := fundef;
       f5_ZF := fundef |}.

  (* -------------------------------------------------------------------- *)
  Definition rflags_of_div :=
    {| f5_OF := fundef; 
       f5_CF := fundef;
       f5_SF := fundef;
       f5_PF := fundef;
       f5_ZF := fundef |}.

  (* -------------------------------------------------------------------- *)
  Definition rflags_of_aluop_nocf (w : int) (vs : Z) :=
    {| f4_OF := flag (signed w != vs);
       f4_SF := SF_of_word w; 
       f4_PF := PF_of_word w; 
       f4_ZF := ZF_of_word w; |}.

  Definition rflags_of_aluop_w (w : int) (vu vs : Z) : (rflags5 * int) :=
    (rflags_of_aluop w vu vs, w).

  Definition rflags_of_aluop_nocf_w (w : int) (vs : Z) :(rflags4 * int) :=
    (rflags_of_aluop_nocf w vs, w).

  Definition rflags_of_bwop_w (w : int) : (rflags5 * int) :=
    (rflags_of_bwop w, w).

  Definition x86_neg (w:int) :=
    let vs := (- signed w)%Z in
    let v := neg w in
    ({| f5_OF := flag (signed v != vs);  
        f5_CF := flag (negb (weq w zero));
        f5_SF := SF_of_word v; 
        f5_PF := PF_of_word v;
        f5_ZF := ZF_of_word v; |}, v).

  Definition x86_add (v1 v2 : int) :=
    rflags_of_aluop_w
    (add v1 v2)
    (unsigned v1 + unsigned v2)%Z
    (signed   v1 + signed   v2)%Z.

  Definition x86_sub (v1 v2 : int) :=
    rflags_of_aluop_w
      (sub v1 v2)
      (unsigned v1 - unsigned v2)%Z
      (signed   v1 - signed   v2)%Z.

  Definition x86_mul (v1 v2:int): (rflags5 * int * int) :=
    let lo := mul v1 v2 in
    let hi := mulhu v1 v2 in
    let ov := dwordu hi lo in
    let ov := (ov >? max_unsigned)%Z in
    (rflags_of_mul ov, hi, lo).

  Definition x86_imul (v1 v2:int) : (rflags5 * int * int) :=
    let lo := mul v1 v2 in
    let hi := mulhs v1 v2 in
    let ov := dwords hi lo in
    let ov := (ov <? min_signed)%Z || (ov >? max_unsigned)%Z in
    (rflags_of_mul ov, hi, lo).

  Definition x86_imul64 (v1 v2:int) : (rflags5 * int) :=
    let lo := mul v1 v2 in
    let hi := mulhs v1 v2 in
    let ov := dwords hi lo in
    let ov := (ov <? min_signed)%Z || (ov >? max_unsigned)%Z in
    (rflags_of_mul ov, lo).

  Definition x86_div (hi lo dv:int) : exec (rflags5 * int * int) :=
    let dd := dwordu hi lo in
    let dv := unsigned dv in
    let q  := (dd  /  dv)%Z in
    let r  := (dd mod dv)%Z in
    let ov := (q >? max_unsigned)%Z in
    if (dv == 0)%Z || ov then type_error else
    ok (rflags_of_div, repr q, repr r).

  Definition x86_idiv (hi lo dv:int) : exec (rflags5 * int * int) :=
    let dd := dwords hi lo in
    let dv := signed dv in
    let q  := (Z.quot dd dv)%Z in
    let r  := (Z.rem  dd dv)%Z in
    let ov := (q <? min_signed)%Z || (q >? max_signed)%Z in
    if (dv == 0)%Z || ov then type_error else
    ok (rflags_of_div, repr q, repr r).

  Definition x86_adc (v1 v2 : int) (c:bool) :=
    let c := b_to_w c in
    rflags_of_aluop_w
      (add_carry v1 v2 c)
      (unsigned v1 + unsigned v2 + unsigned c)%Z
      (signed   v1 + signed   v2 + unsigned c)%Z.

  Definition x86_sbb (v1 v2 : int) (c:bool) :=
    let c := b_to_w c in
    rflags_of_aluop_w
      (sub_borrow v1 v2 c)
      (unsigned v1 - (unsigned v2 + unsigned c))%Z
      (signed   v1 - (signed   v2 + unsigned c))%Z.

  Definition x86_inc (w:int) :=
    rflags_of_aluop_nocf_w
      (add w one)
      (signed w + 1)%Z.

  Definition x86_dec (w:int) :=
    rflags_of_aluop_nocf_w
      (sub w one)
      (signed w - 1)%Z.

  Definition x86_setcc (b:bool) : int := (b_to_w b).

  Definition x86_test (x y: int) : rflags5 :=
    (rflags_of_bwop (and x y)).

  Definition x86_cmp (x y: int) :=
    rflags_of_aluop 
      (sub x y)
      (unsigned x - unsigned y)%Z 
      (signed x - signed y)%Z.

  Definition x86_and (v1 v2: int) :=
    rflags_of_bwop_w
      (and v1 v2).

  Definition x86_or (v1 v2: int) :=
    rflags_of_bwop_w
      (or v1 v2).

  Definition x86_xor (v1 v2: int) :=
    rflags_of_bwop_w
      (xor v1 v2).

  Definition x86_not (v:int) :=
    not v.

  Definition x86_shl OF CF SF PF ZF (v i: int) : rflags5 * int :=
    let i := and i (repr WS.x86_shift_zmask) in
    if i == zero then
      ({| f5_OF := OF; 
          f5_CF := CF; 
          f5_SF := SF; 
          f5_PF := PF; 
          f5_ZF := ZF |}, v)
    else
      let rc := msb (shl v (sub i one)) in
      let r  := shl v i in
      ({| f5_OF :=
           if i == one then flag (msb r (+) rc)
           else fundef;
         f5_CF := flag rc;
         f5_SF := flag (SF_of_word r);
         f5_PF := flag (PF_of_word r);
         f5_ZF := flag (ZF_of_word r); |}, r).

  Definition x86_shr OF CF SF PF ZF (v i: int) : rflags5 * int :=
    let i := and i (repr WS.x86_shift_zmask) in
    if i == zero then
      ({| f5_OF := OF; 
          f5_CF := CF; 
          f5_SF := SF; 
          f5_PF := PF; 
          f5_ZF := ZF |}, v)
    else
      let rc := lsb (shru v (sub i one)) in
      let r  := shru v i in
      ({| f5_OF :=
            if i == one then flag (msb r)
            else fundef;
          f5_CF := flag rc;
          f5_SF := flag (SF_of_word r);
          f5_PF := flag (PF_of_word r);
          f5_ZF := flag (ZF_of_word r) |}, r).

  Definition x86_sar OF CF SF PF ZF (v i: int) : rflags5 * int :=
    let i := and i (repr WS.x86_shift_zmask) in
    if i == zero then
      ({| f5_OF := OF; 
          f5_CF := CF; 
          f5_SF := SF; 
          f5_PF := PF; 
          f5_ZF := ZF |}, v)
    else
      let rc := lsb (shr v (sub i one)) in
      let r  := shr v i in
      ({| f5_OF :=
           if i == one then ffalse
           else fundef;
          f5_CF := flag rc;
          f5_SF := flag (SF_of_word r);
          f5_PF := flag (PF_of_word r);
          f5_ZF := flag (ZF_of_word r) |}, r).

  Definition x86_rcl (CF:bool) (v i0: int) := 
    let i := (and i0 (repr WS.x86_shift_zmask)) mod WS.x86_rotate_mod in
    let x := unsigned v * 2 + Zofb CF in
    let x := Z.lor (Z.shiftl x i) (Z.shiftr x (zwordsize + 1 - i)) in

    let r := repr (Z.shiftr x 1) in
    let CF := x <? 0 in
    let OF := 
      if i0 == one then Some (xorb (msb r) CF)
      else None in
    ({| f2_OF := OF;
        f2_CF := Some CF |}, r).

  Definition x86_rcr (CF:bool) (v i0: int) := 
    let i := (and i0 (repr WS.x86_shift_zmask)) mod WS.x86_rotate_mod in
    let OF := 
      if i0 == one then Some (xorb (msb v) CF)
      else None in

    let x := Zofb CF *  modulus + unsigned v in
    let x := Z.lor (Z.shiftr x i) (Z.shiftl x (zwordsize + 1 - i)) in
    let r := repr x in
    let CF := x <? 0 in
     ({| f2_OF := OF;
         f2_CF := Some CF |}, r).

  Definition x86_rol (v i0: int) := 
    let i := and i0 (repr WS.x86_shift_zmask) mod zwordsize in
    let r := rol v (repr i) in
    let CF := lsb r in
    let OF := 
      if  and i0 (repr WS.x86_shift_zmask) == one then Some (xorb (msb r) CF)
      else None in
    ({| f2_OF := OF;
        f2_CF := Some CF |}, r).

  Definition x86_ror (v i0: int) := 
    let i := and i0 (repr WS.x86_shift_zmask) mod zwordsize in
    let r := ror v (repr i) in
    let CF := msb r in
    let OF := 
      if and i0 (repr WS.x86_shift_zmask) == one then 
       (* FIXME what is the value here *)
          Some (xorb (msb r) CF)
      else None in
    ({| f2_OF := OF;
        f2_CF := Some CF |}, r).

  Definition x86_rorx (v i: int) := 
    let i := and i (repr WS.x86_shift_zmask) in
    let r := ror v (repr i) in
    r.
  
End MakeI.

Module I8   := MakeI Wordsize_8.
Module I16  := MakeI Wordsize_16.
Module I32  := MakeI Wordsize_32.
Module I64  := MakeI Wordsize_32.

Export I8.Theory I16.Theory I32.Theory I64.Theory.

Notation word := I64.int (only parsing).

Inductive wsize := 
  | U8 
  | U16
  | U32 
  | U64.

Scheme Equality for wsize.

Lemma wsize_eq_axiom : Equality.axiom wsize_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_wsize_dec_bl.
  by apply: internal_wsize_dec_lb.
Qed.

Definition wsize_eqMixin     := Equality.Mixin wsize_eq_axiom.
Canonical  wsize_eqType      := Eval hnf in EqType wsize wsize_eqMixin.

Definition i_wsize (s:wsize) := 
  match s with
  | U8     => I8.int
  | U16    => I16.int
  | U32    => I32.int
  | U64    => I64.int
  end.

Definition wsize_size (s:wsize) := 
  match s with
  | U8     => 1%Z
  | U16    => 2%Z
  | U32    => 4%Z
  | U64    => 8%Z
  end.

Definition of_word ws (w:word) : i_wsize ws :=
  match ws with
  | U8  => I8 .repr (I64.unsigned w)
  | U16 => I16.repr (I64.unsigned w)
  | U32 => I32.repr (I64.unsigned w)
  | U64 => w
  end.

Definition w_to_word ws : i_wsize ws -> word :=
  match ws with
  | U8  => fun w => I64.repr (I8 .unsigned w)
  | U16 => fun w => I64.repr (I16.unsigned w)
  | U32 => fun w => I64.repr (I32.unsigned w)
  | U64 => fun w => w
  end.

Definition w_op1 ws (op:i_wsize ws -> i_wsize ws) (w:word) :=
  w_to_word (op (of_word ws w)).

Definition select_op (T : wsize -> Type) o8 o16 o32 o64 ws := 
  match ws return T ws with
  | U8  => o8 
  | U16 => o16 
  | U32 => o32 
  | U64 => o64
  end.

Definition wrepr ws z := 
  w_to_word (@select_op (fun ws => Z -> i_wsize ws) I8.repr I16.repr I32.repr I64.repr ws z).
  
Definition wlnot ws := 
  w_op1 (@select_op (fun w => i_wsize w -> i_wsize w) I8.not I16.not I32.not I64.not ws).

Definition wneg ws := 
  w_op1 (@select_op (fun w => i_wsize w -> i_wsize w) I8.neg I16.neg I32.neg I64.neg ws).

Definition w_op2 ws (op : i_wsize ws -> i_wsize ws -> i_wsize ws) (w1 w2:word) :=
  w_to_word (op (of_word ws w1) (of_word ws w2)).

Definition w_op2b ws (op : i_wsize ws -> i_wsize ws -> bool -> bool * i_wsize ws) 
           (w1 w2:word) (b:bool) :=
  let bw := op (of_word ws w1) (of_word ws w2) b in
  (bw.1, w_to_word bw.2).

Definition w_op2ww ws (op : i_wsize ws -> i_wsize ws -> i_wsize ws * i_wsize ws) 
           (w1 w2:word) :=
  let ww := op (of_word ws w1) (of_word ws w2) in
  (w_to_word ww.1, w_to_word ww.2).

Definition w_op2_b ws (op: i_wsize ws -> i_wsize ws -> bool) (w1 w2:word) :=
  op (of_word ws w1) (of_word ws w2).

Definition wadd w := 
  w_op2 (@select_op (fun w => i_wsize w -> i_wsize w -> i_wsize w) 
    I8.add I16.add I32.add I64.add w).

Definition wmul w := 
  w_op2 (@select_op (fun w => i_wsize w -> i_wsize w -> i_wsize w) 
    I8.mul I16.mul I32.mul I64.mul w).

Definition wsub w := 
  w_op2 (@select_op (fun w => i_wsize w -> i_wsize w -> i_wsize w) 
    I8.sub I16.sub I32.sub I64.sub w).

Definition wland w :=
  w_op2 (@select_op (fun w => i_wsize w -> i_wsize w -> i_wsize w) 
    I8.and I16.and I32.and I64.and w).

Definition wlor w := 
  w_op2 (@select_op (fun w => i_wsize w -> i_wsize w -> i_wsize w) 
    I8.or  I16.or  I32.or  I64.or  w).

Definition wlxor w := 
  w_op2 (@select_op (fun w => i_wsize w -> i_wsize w -> i_wsize w) 
    I8.xor I16.xor I32.xor I64.xor w).

Definition wlsr w := 
  w_op2 (@select_op (fun w => i_wsize w -> i_wsize w -> i_wsize w) 
    I8.sem_lsr I16.sem_lsr I32.sem_lsr I64.sem_lsr w).

Definition wlsl w := 
  w_op2 (@select_op (fun w => i_wsize w -> i_wsize w -> i_wsize w) 
    I8.sem_lsl I16.sem_lsl I32.sem_lsl I64.sem_lsl w).

Definition wasr w := 
  w_op2 (@select_op (fun w => i_wsize w -> i_wsize w -> i_wsize w) 
    I8.sem_asr I16.sem_asr I32.sem_asr I64.sem_asr w).

Definition weq w := 
  w_op2_b (@select_op (fun w => i_wsize w -> i_wsize w -> bool)
    I8.weq I16.weq I32.weq I64.weq w).

Definition wneq w := 
  w_op2_b 
    (fun x y => negb (@select_op (fun w => i_wsize w -> i_wsize w -> bool)
                        I8.weq I16.weq I32.weq I64.weq w x y)).

Definition wslt w := 
  w_op2_b (@select_op (fun w => i_wsize w -> i_wsize w -> bool)
             I8.wslt I16.wslt I32.wslt I64.wslt w).

Definition wult w := 
  w_op2_b (@select_op (fun w => i_wsize w -> i_wsize w -> bool)
             I8.wult I16.wult I32.wult I64.wult w).

Definition wsle w := 
  w_op2_b (@select_op (fun w => i_wsize w -> i_wsize w -> bool)
             I8.wsle I16.wsle I32.wsle I64.wsle w).

Definition wule w := 
  w_op2_b (@select_op (fun w => i_wsize w -> i_wsize w -> bool)
             I8.wule I16.wule I32.wule I64.wule w).

Definition wsgt w := 
  w_op2_b 
    (fun x y => @select_op (fun w => i_wsize w -> i_wsize w -> bool)
                  I8.wslt I16.wslt I32.wslt I64.wslt w y x).

Definition wugt w := 
  w_op2_b 
    (fun x y => @select_op (fun w => i_wsize w -> i_wsize w -> bool)
                  I8.wult I16.wult I32.wult I64.wult w y x).

Definition wsge w := 
  w_op2_b 
    (fun x y => @select_op (fun w => i_wsize w -> i_wsize w -> bool)
                  I8.wsle I16.wsle I32.wsle I64.wsle w y x).

Definition wuge w := 
  w_op2_b 
    (fun x y => @select_op (fun w => i_wsize w -> i_wsize w -> bool)
                  I8.wule I16.wule I32.wule I64.wule w y x).

Definition waddc w :=
  w_op2b (@select_op (fun ws => i_wsize ws -> i_wsize ws -> bool -> bool * i_wsize ws)
     I8.waddc I16.waddc I32.waddc I64.waddc w).

Definition wsubc w :=
  w_op2b (@select_op (fun ws => i_wsize ws -> i_wsize ws -> bool -> bool * i_wsize ws)
     I8.wsubc I16.wsubc I32.wsubc I64.wsubc w).

Definition wmulu w :=
  w_op2ww (@select_op (fun ws => i_wsize ws -> i_wsize ws -> i_wsize ws * i_wsize ws)
      I8.wmulu I16.wmulu I32.wmulu I64.wmulu w).

Definition wmuls w := 
  w_op2ww (@select_op (fun ws => i_wsize ws -> i_wsize ws -> i_wsize ws * i_wsize ws)
      I8.wmuls I16.wmuls I32.wmuls I64.wmuls w).

(* ** Machine word representation for the compiler and the wp
 * -------------------------------------------------------------------- *)
Definition bwbz (bw:bool * word) : bool * Z := 
  (bw.1, I64.unsigned bw.2).

Definition wwzz (bw:word * word) : Z * Z := 
  (I64.unsigned bw.1, I64.unsigned bw.2).

Definition iword_wlnot ws z1    :=  I64.unsigned (wlnot ws (I64.repr z1)).
Definition iword_wneg  ws z1    :=  I64.unsigned (wneg  ws (I64.repr z1)).
Definition iword_wadd  ws z1 z2 :=  I64.unsigned (wadd  ws (I64.repr z1) (I64.repr z2)).
Definition iword_wmul  ws z1 z2 :=  I64.unsigned (wmul  ws (I64.repr z1) (I64.repr z2)).
Definition iword_wsub  ws z1 z2 :=  I64.unsigned (wsub  ws (I64.repr z1) (I64.repr z2)).
Definition iword_wland ws z1 z2 :=  I64.unsigned (wland ws (I64.repr z1) (I64.repr z2)).
Definition iword_wlor  ws z1 z2 :=  I64.unsigned (wlor  ws (I64.repr z1) (I64.repr z2)).
Definition iword_wlxor ws z1 z2 :=  I64.unsigned (wlxor ws (I64.repr z1) (I64.repr z2)).
Definition iword_wlsr  ws z1 z2 :=  I64.unsigned (wlsr  ws (I64.repr z1) (I64.repr z2)).
Definition iword_wlsl  ws z1 z2 :=  I64.unsigned (wlsl  ws (I64.repr z1) (I64.repr z2)).
Definition iword_wasr  ws z1 z2 :=  I64.unsigned (wasr  ws (I64.repr z1) (I64.repr z2)).
Definition iword_weq   ws z1 z2 :=  weq  ws (I64.repr z1) (I64.repr z2).
Definition iword_wneq  ws z1 z2 :=  wneq ws (I64.repr z1) (I64.repr z2).
Definition iword_wslt  ws z1 z2 :=  wslt ws (I64.repr z1) (I64.repr z2).
Definition iword_wult  ws z1 z2 :=  wult ws (I64.repr z1) (I64.repr z2).
Definition iword_wsle  ws z1 z2 :=  wsle ws (I64.repr z1) (I64.repr z2).
Definition iword_wule  ws z1 z2 :=  wule ws (I64.repr z1) (I64.repr z2).
Definition iword_wsgt  ws z1 z2 :=  wsgt ws (I64.repr z1) (I64.repr z2).
Definition iword_wugt  ws z1 z2 :=  wugt ws (I64.repr z1) (I64.repr z2).
Definition iword_wsge  ws z1 z2 :=  wsge ws (I64.repr z1) (I64.repr z2).
Definition iword_wuge  ws z1 z2 :=  wuge ws (I64.repr z1) (I64.repr z2).
Definition iword_wmulu ws z1 z2 :=  wwzz (wmulu ws (I64.repr z1) (I64.repr z2)).
Definition iword_wmuls ws z1 z2 :=  wwzz (wmuls ws (I64.repr z1) (I64.repr z2)).
Definition iword_waddc ws z1 z2 b := bwbz (waddc ws (I64.repr z1) (I64.repr z2) b).
Definition iword_wsubc ws z1 z2 b := bwbz (wsubc ws (I64.repr z1) (I64.repr z2) b).

(* ** Coercion to nat 
 * -------------------------------------------------------------------- *)

Definition w2n (x:word) := Z.to_nat (I64.unsigned x).
Definition n2w (n:nat) := I64.repr (Z.of_nat n).

