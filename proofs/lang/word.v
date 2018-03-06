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
From CoqWord Require Import xword.
Require ssrring.
Require Import Psatz ZArith utils type.
Import Utf8.
Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

(* ** Machine word representation for proof 
 * -------------------------------------------------------------------- *)

(*
Notation word := I64.int (only parsing).

Coercion I64.unsigned : I64.int >-> Z.

(* Notation wadd := I64.add (only parsing). *)

Definition Zofb (b:bool) := if b then 1 else 0.

Definition waddcarry (x y:word) (c:bool) :=
  let n := I64.unsigned x + I64.unsigned y + Zofb c in
  (I64.modulus <=? n, I64.repr n).

Notation wsub := I64.sub (only parsing).

Definition wsubcarry (x y:word) (c:bool) :=
  let n := I64.unsigned x - I64.unsigned y - Zofb c in
  (n <? 0, I64.repr n).

Definition wumul (x y: word) := 
  let n := I64.unsigned x * I64.unsigned y in
  (I64.repr (Z.quot n I64.modulus), I64.repr n).
  
Definition weq (x y:word) := I64.unsigned x =? I64.unsigned y.

Definition wsle (x y:word) := I64.signed x <=? I64.signed y.
Definition wslt (x y:word) := I64.signed x <? I64.signed y.

Definition wule (x y:word) := I64.unsigned x <=? I64.unsigned y.
Definition wult (x y:word) := I64.unsigned x <? I64.unsigned y.

Lemma lt_unsigned x: (I64.modulus <=? I64.unsigned x)%Z = false.
Proof. by rewrite Z.leb_gt;case: (I64.unsigned_range x). Qed.

Lemma le_unsigned x: (0 <=? I64.unsigned x)%Z = true.
Proof. by rewrite Z.leb_le;case: (I64.unsigned_range x). Qed.

Lemma unsigned0 : I64.unsigned (I64.repr 0) = 0%Z.
Proof. by rewrite I64.unsigned_repr. Qed.

Lemma weq_refl x : weq x x.
Proof. by rewrite /weq Z.eqb_refl. Qed.

Lemma wsle_refl x : wsle x x.
Proof. by rewrite /wsle Z.leb_refl. Qed.

Lemma wule_refl x : wule x x.
Proof. by rewrite /wule Z.leb_refl. Qed.

Lemma wslt_irrefl x : wslt x x = false.
Proof. by rewrite /wslt Z.ltb_irrefl. Qed.

Lemma wult_irrefl x : wult x x = false.
Proof. by rewrite /wult Z.ltb_irrefl. Qed.

(* ** Coercion to nat 
 * -------------------------------------------------------------------- *)

Definition w2n (x:word) := Z.to_nat (I64.unsigned x).
Definition n2w (n:nat) := I64.repr (Z.of_nat n).

(* ** Machine word representation for the compiler and the wp
 * -------------------------------------------------------------------- *)

Notation iword := Z (only parsing).

Notation ibase := I64.modulus (only parsing).

Notation tobase := I64.Z_mod_modulus (only parsing).

Lemma reqP n1 n2: reflect (I64.repr n1 = I64.repr n2) (tobase n1 == tobase n2).
Proof. by apply ueqP. Qed.

Definition iword_eqb (n1 n2:iword) := 
  (tobase n1 =? tobase n2).

Definition iword_ltb (n1 n2:iword) : bool:= 
  (tobase n1 <? tobase n2).

Definition iword_leb (n1 n2:iword) : bool:= 
  (tobase n1 <=? tobase n2).

Definition iword_add (n1 n2:iword) : iword := tobase (n1 + n2).

Definition iword_addc (n1 n2:iword) : (bool * iword) := 
  let n  := tobase n1 + tobase n2 in
  (ibase <=? n, tobase n).

Definition iword_addcarry (n1 n2:iword) (c:bool) : (bool * iword) := 
  let n  := tobase n1 + tobase n2 + Zofb c in
  (ibase <=? n, tobase n).

Definition iword_sub (n1 n2:iword) : iword := tobase (n1 - n2).

Definition iword_subc (n1 n2:iword) : (bool * iword) := 
  let n := tobase n1 - tobase n2 in
  (n <? 0, tobase n).

Definition iword_subcarry (n1 n2:iword) (c:bool) : (bool * iword) := 
  let n := tobase n1 - tobase n2 - Zofb c in
  (n <? 0, tobase n).

Definition iword_mul (n1 n2:iword) : iword := tobase (n1 * n2).

Lemma iword_eqbP (n1 n2:iword) : iword_eqb n1 n2 = (I64.repr n1 == I64.repr n2).
Proof. by []. Qed.

Lemma iword_ltbP (n1 n2:iword) : iword_ltb n1 n2 = wult (I64.repr n1) (I64.repr n2).
Proof. by []. Qed.

Lemma iword_lebP (n1 n2:iword) : iword_leb n1 n2 = wule (I64.repr n1) (I64.repr n2).
Proof. by []. Qed.

Lemma urepr n : I64.unsigned (I64.repr n) = I64.Z_mod_modulus n.
Proof. done. Qed.

Lemma repr_mod n : I64.repr (I64.Z_mod_modulus n) = I64.repr n.
Proof. by apply: reqP;rewrite !I64.Z_mod_modulus_eq Zmod_mod. Qed.

Lemma iword_addP (n1 n2:iword) : 
  I64.repr (iword_add n1 n2) = wadd (I64.repr n1) (I64.repr n2).
Proof. 
  apply: reqP;rewrite /iword_add /I64.add !urepr.
  by rewrite !I64.Z_mod_modulus_eq Zmod_mod Zplus_mod.
Qed.

Lemma iword_addcarryP (n1 n2:iword) c : 
  let r := iword_addcarry n1 n2 c in
  (r.1, I64.repr r.2) = waddcarry (I64.repr n1) (I64.repr n2) c.
Proof. by rewrite /iword_addcarry /waddcarry !urepr /= repr_mod. Qed.

Lemma iword_subP (n1 n2:iword) : 
  I64.repr (iword_sub n1 n2) = wsub (I64.repr n1) (I64.repr n2).
Proof.
  apply: reqP;rewrite /iword_sub /I64.sub !urepr.
  by rewrite !I64.Z_mod_modulus_eq Zmod_mod Zminus_mod.
Qed.

Lemma iword_subcarryP (n1 n2:iword) c : 
  let r := iword_subcarry n1 n2 c in
  (r.1, I64.repr r.2) = wsubcarry (I64.repr n1) (I64.repr n2) c.
Proof. by rewrite /iword_subcarry /wsubcarry !urepr /= repr_mod. Qed.

Lemma iword_mulP (n1 n2:iword) : 
  I64.repr (iword_mul n1 n2) = I64.mul (I64.repr n1) (I64.repr n2).
Proof.
  apply: reqP;rewrite /iword_mul /I64.mul !urepr.
  by rewrite !I64.Z_mod_modulus_eq Zmod_mod Zmult_mod.
Qed.

*)
(* --------------------------------------------------------------------------- *)

(*
Module Wordsize_16.
  Definition wordsize : nat := 16.
  Lemma wordsize_not_zero : wordsize <> 0%nat.
  Proof. done. Qed.
End Wordsize_16.

Module Wordsize_128.
  Definition wordsize : nat := 128.
  Lemma wordsize_not_zero : wordsize <> 0%nat.
  Proof. done. Qed.
End Wordsize_128.

Module Wordsize_256.
  Definition wordsize : nat := 256.
  Lemma wordsize_not_zero : wordsize <> 0%nat.
  Proof. done. Qed.
End Wordsize_256.

Module I8 := Integers.Byte.
Module I16 := Integers.Make Wordsize_16.
Module I32 := Integers.Int.
Module I128 := Integers.Make Wordsize_128.
Module I256 := Integers.Make Wordsize_256.

Definition word (s:wsize) := 
  match s with
  | U8     => I8.int
  | U16    => I16.int
  | U32    => I32.int
  | U64    => I64.int
  | U128   => I128.int
  | U256   => I256.int
  end.

Definition wsize_size (s:wsize) := 
  match s with
  | U8     => 1%Z
  | U16    => 2%Z
  | U32    => 4%Z
  | U64    => 8%Z
  | U128   => 16%Z
  | U256   => 32%Z
  end.


Definition wzero  (s:wsize) : word s := 
  match s with
  | U8     => I8.zero
  | U16    => I16.zero
  | U32    => I32.zero
  | U64    => I64.zero
  | U128   => I128.zero
  | U256   => I256.zero
  end.

Definition wunsigned (s:wsize) : word s -> Z := 
   match s with
  | U8     => I8.unsigned
  | U16    => I16.unsigned
  | U32    => I32.unsigned
  | U64    => I64.unsigned
  | U128   => I128.unsigned
  | U256   => I256.unsigned
  end.

Definition wrepr (s:wsize) : Z -> word s := 
   match s return Z -> word s with
  | U8     => I8.repr
  | U16    => I16.repr
  | U32    => I32.repr
  | U64    => I64.repr
  | U128   => I128.repr
  | U256   => I256.repr
  end.
  
Lemma wrepr_unsigned s (w: word s) :  wrepr s (wunsigned w) = w.
Proof.
  refine (match s return forall w, wrepr s (wunsigned w) = w with
  | U8     => I8.repr_unsigned
  | U16    => I16.repr_unsigned
  | U32    => I32.repr_unsigned
  | U64    => I64.repr_unsigned
  | U128   => I128.repr_unsigned
  | U256   => I256.repr_unsigned
  end w).
Qed.

*)

Definition nat7 : nat := 7.
Definition nat15 : nat := nat7.+4.+4.
Definition nat31 : nat := nat15.+4.+4.+4.+4.
Definition nat63 : nat := nat31.+4.+4.+4.+4.+4.+4.+4.+4.
Definition nat127 : nat := nat63.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.
Definition nat255 : nat := nat127.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.

Definition wsize_size_minus_1 (s: wsize) : nat :=
  match s with
  | U8 => nat7
  | U16 => nat15
  | U32 => nat31
  | U64 => nat63
  | U128 => nat127
  | U256 => nat255
  end.

Definition wsize_bits (s:wsize) : Z :=
  Zpos (Pos.of_succ_nat (wsize_size_minus_1 s)).

Definition wsize_size (sz: wsize) : Z :=
  wsize_bits sz / 8.

Lemma wsize_size_pos sz :
  0 < wsize_size sz.
Proof. by case sz. Qed.

Definition word : wsize -> comRingType :=
  λ sz, word_comRingType (wsize_size_minus_1 sz).

Global Opaque word.

Definition wand {s} (x y: word s) : word s := wand x y.
Definition wor {s} (x y: word s) : word s := wor x y.
Definition wxor {s} (x y: word s) : word s := wxor x y.

Parameters wmulhu wmulhs : forall {s}, word s -> word s -> word s.

Parameter wshr wshl wsar : forall {s}, word s -> Z -> word s.

Definition wlt {sz} (sg: signedness) : word sz → word sz → bool :=
  match sg with
  | Unsigned => λ x y, (urepr x < urepr y)%R
  | Signed => λ x y, (srepr x < srepr y)%R
  end.

Parameter wle : forall {s}, signedness -> word s -> word s -> bool.

Parameter wnot : forall {s}, word s -> word s.

Definition wbase (s: wsize) : Z :=
  modulus (wsize_size_minus_1 s).+1.

Definition wunsigned {s} (w: word s) : Z :=
  urepr w.

Definition wsigned {s} (w: word s) : Z :=
  srepr w.

Definition wrepr s (z: Z) : word s :=
  mkword (wsize_size_minus_1 s).+1 z.

Lemma wrepr_unsigned s (w: word s) : wrepr s (wunsigned w) = w.
Proof. by rewrite /wrepr /wunsigned ureprK. Qed.

Lemma wunsigned_range sz (p: word sz) :
  0 <= wunsigned p < wbase sz.
Proof. by have /iswordZP := isword_word p. Qed.

Lemma wunsigned_add sz (p: word sz) (n: Z) :
  0 <= wunsigned p + n < wbase sz →
  wunsigned (p + wrepr sz n) = wunsigned p + n.
Proof.
case: p => p i h.
change (toword (add_word (mkWord i) (wrepr sz n)) = p + n).
rewrite/add_word mkwordK/= /urepr/=.
rewrite Zplus_mod_idemp_r.
exact: Zmod_small.
Qed.

Axiom wlt_irrefl : ∀ sz sg (w: word sz), wlt sg w w = false.
Axiom wle_refl : ∀ sz sg (w: word sz), wle sg w w = true.

Lemma wshr0 sz (w: word sz) : wshr w 0 = w.
Proof. Admitted.

Lemma wshl0 sz (w: word sz) : wshl w 0 = w.
Proof. Admitted.

Lemma wsar0 sz (w: word sz) : wsar w 0 = w.
Proof. Admitted.

Lemma wmulE sz (x y: word sz) : (x * y)%R = wrepr sz (wunsigned x * wunsigned y).
Proof. Admitted.

Lemma wmulhuE sz (x y: word sz) : wmulhu x y = wrepr sz (wunsigned x * wunsigned y ÷ wbase sz).
Proof. (* I64.mulhu w1 w2 = I64.repr (w1 * w2 ÷ I64.modulus).
Proof.
    rewrite /I64.mulhu.
    case: w1 w2 => [z1 h1] [z2 h2] /=.
    rewrite Zquot.Zquot_Zdiv_pos //.
    apply: Z.mul_nonneg_nonneg; lia. *)
Admitted.

Definition wmax_unsigned sz := wbase sz - 1.
Parameter wmin_signed   : wsize -> Z.
Parameter wmax_signed   : wsize -> Z.

Notation u8   := (word U8).
Notation u16  := (word U16).
Notation u32  := (word U32).
Notation u64  := (word U64).
Notation u128 := (word U128).
Notation u256 := (word U256).

Definition x86_shift_mask (s:wsize) : u8 :=
  match s with 
  | U8 | U16 | U32 => wrepr U8 31
  | U64  => wrepr U8 63
  | U128 => wrepr U8 127
  | U256 => wrepr U8 255
  end%Z.

Definition wbit_n sz (w:word sz) (n:nat) : bool := 
   wbit (wunsigned w) n.

Definition lsb {s} (w: word s) : bool := wbit_n w 0.
Definition msb {s} (w: word s) : bool := wbit_n w (wsize_size_minus_1 s).

Parameters wdwordu wdwords : ∀ s, word s → word s → Z.

Definition waddcarry sz (x y: word sz) (c: bool) :=
  let n := wunsigned x + wunsigned y + Z.b2z c in
  (wbase sz <=? n, wrepr sz n).

Definition wsubcarry sz (x y: word sz) (c: bool) :=
  let n := wunsigned x - wunsigned y - Z.b2z c in
  (n <? 0, wrepr sz n).

Definition wumul sz (x y: word sz) :=
  let n := wunsigned x * wunsigned y in
  (wrepr sz (Z.quot n (wbase sz)), wrepr sz n).

Definition zero_extend sz sz' (w: word sz') : word sz :=
  wrepr sz (wunsigned w).

Definition wbit sz (w i: word sz) : bool :=
  wbit_n w (Z.to_nat (wunsigned i mod wsize_bits sz)).

Definition wror sz (w:word sz) (z:Z) := 
  let i := z mod wsize_bits sz in
  wor (wshr w i) (wshl w (wsize_bits sz - i)).

Definition wrol sz (w:word sz) (z:Z) := 
  let i := z mod wsize_bits sz in
  wor (wshl w i) (wshr w (wsize_bits sz - i)).

(* -------------------------------------------------------------------*)

Lemma wltE sg sz (w1 w2: word sz) :
  wlt sg w1 w2 = (wunsigned (w1 - w2) != (wunsigned w1 - wunsigned w2))%Z.
Proof. Admitted.

Lemma wltuE' sz (α β: word sz) :
  wlt Unsigned α β = (wunsigned (β - α) == (wunsigned β - wunsigned α)%Z) && (β != α).
Proof. Admitted.

Lemma wleuE sz (w1 w2: word sz) :
  wle Unsigned w1 w2 = (wunsigned (w2 - w1) == (wunsigned w2 - wunsigned w1))%Z.
Proof. Admitted.

Lemma wleuE' sz (α β: word sz) :
  wle Unsigned β α = (wunsigned (β - α) != (wunsigned β - wunsigned α)%Z) || (β == α).
Proof. Admitted.

Lemma wlesE sz (w1 w2: word sz) :
  wle Signed w1 w2 = (msb (w2 - w1) == (wsigned (w2 - w1) != (wsigned w2 - wsigned w1)%Z)).
Proof. Admitted.

(* -------------------------------------------------------------------*)

Lemma wsize_cmpP sz sz' :
  wsize_cmp sz sz' = Nat.compare (wsize_size_minus_1 sz) (wsize_size_minus_1 sz').
Proof. by case: sz sz' => -[]; vm_compute. Qed.

Lemma zero_extend_u sz (w:word sz) : zero_extend sz w = w.
Proof. by rewrite /zero_extend wrepr_unsigned. Qed.


Ltac elim_div :=
   unfold Zdiv, Zmod;
     match goal with
       |  H : context[ Zdiv_eucl ?X ?Y ] |-  _ =>
          generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
       |  |-  context[ Zdiv_eucl ?X ?Y ] =>
          generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
     end; unfold Remainder.

Lemma mod_pq_mod_q x p q :
  0 < p → 0 < q →
  (x mod (p * q)) mod q = x mod q.
Proof.
move => hzp hzq.
have hq : q ≠ 0 by nia.
have hpq : p * q ≠ 0 by nia.
elim_div => /(_ hq); elim_div => /(_ hpq) => [] [?] hr1 [?] hr2; subst.
elim_div => /(_ hq) [heq hr3].
intuition (try nia).
suff : p * z1 + z = z2; nia.
Qed.

Lemma word_ext n x y h h' :
  x = y →
  @mkWord n x h = @mkWord n y h'.
Proof. by move => e; apply/val_eqP/eqP. Qed.

Lemma wunsigned_inj sz : injective (@wunsigned sz).
Proof. by move => x y /eqP /val_eqP. Qed.

Lemma zero_extend_wrepr sz sz' z :
  (sz <= sz')%CMP →
  zero_extend sz (wrepr sz' z) = wrepr sz z.
Proof.
move=> /eqP; rewrite /cmp_le /gcmp wsize_cmpP Nat.compare_ge_iff => hle.
apply: word_ext.
rewrite /wunsigned /urepr /wrepr /=.
move: hle. set a := wsize_size_minus_1 sz; set b := wsize_size_minus_1 sz' => hle.
have : ∃ n, modulus b.+1 = modulus n * modulus a.+1.
- exists (b - a)%nat; rewrite /modulus !two_power_nat_equiv -Z.pow_add_r; try lia.
  rewrite (Nat2Z.inj_sub _ _ hle); f_equal; lia.
case => n -> {hle b}.
exact: mod_pq_mod_q.
Qed.

Lemma zero_extend_idem s s1 s2 (w:word s) : 
  (s1 <= s2)%CMP -> zero_extend s1 (zero_extend s2 w) = zero_extend s1 w.
Proof.
  by move=> hle;rewrite [X in (zero_extend _ X) = _]/zero_extend zero_extend_wrepr.
Qed.

(* -------------------------------------------------------------------*)

Ltac wring := 
  rewrite ?zero_extend_u; ssrring.ssring.

(* -------------------------------------------------------------------*)
Definition check_scale (s:Z) :=
  (s == 1%Z) || (s == 2%Z) || (s == 4%Z) || (s == 8%Z).

(* -------------------------------------------------------------------*)

Definition mask_word (sz:wsize) : u64 := 
  match sz with
  | U8 | U16 => wshl (wrepr _ (-1)) (wsize_bits sz)
  | _ => 0%R
  end.

Definition merge_word (wr: u64) (sz:wsize) (w:word sz) := 
   wxor (wand (mask_word sz) wr) (zero_extend U64 w).
