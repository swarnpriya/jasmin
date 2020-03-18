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

(** This defines an example instance of the memory model.

The stack grows towards lower addresses, from the root to the bottom.

The stack is full when the “top” reaches address zero.

Stack frames have sizes that are multiple of 32 and the stack root is aligned at a multiple of 32 bytes.

*)

Require memory_model array type.

Import Utf8.
Import all_ssreflect all_algebra.
Import ZArith.
Import ssrZ.
Import type word utils gen_map.
Import memory_model.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma zip_nil S T (m: seq T) : zip [::] m = @ nil (S * T).
Proof. by case: m. Qed.

Lemma cut_wbase_Uptr sz :
  wbase Uptr = (wsize_size sz * CoqWord.word.modulus (nat63.+3 - (Nat.log2 (wsize_size_minus_1 sz))))%Z.
Proof. by case: sz; vm_compute. Qed.

Local Open Scope Z_scope.

Lemma wsize_size_le a b :
  (a ≤ b)%CMP →
  (wsize_size a | wsize_size b).
Proof.
  case: a; case: b => // _.
  1, 7, 12, 16, 19, 21: by exists 1.
  1, 6, 10, 13, 15: by exists 2.
  1, 5, 8, 10: by exists 4.
  1, 4, 6: by exists 8.
  1, 3: by exists 16.
  by exists 32.
Qed.

Lemma aligned_factor s n :
  s != 0 →
  reflect (∃ q, n = q * s) (n mod s == 0).
Proof.
  move => /eqP s_pos; case: eqP => /Zmod_divides => - /(_ s_pos) h; constructor.
  - case: h => c; exists c; Psatz.lia.
  case => c ?; apply: h; exists c; Psatz.lia.
Qed.

(* -------------------------------------------------------------------------- *)

Module Align.

Local Notation is_align ptr ws :=
  (let w := wunsigned ptr in
  (w mod wsize_size ws == 0)%Z).

Lemma is_align_array ptr sz j :
  is_align ptr sz → is_align (wrepr U64 (wsize_size sz * j) + ptr) sz.
Proof.
  have hn := wsize_size_pos sz.
  have hnz : wsize_size sz ≠ 0%Z by Psatz.lia.
  move => /eqP /Zmod_divides [] // p hptr.
  rewrite /wunsigned CoqWord.word.addwE -!/(wunsigned _) Zplus_mod hptr -Zplus_mod.
  rewrite wunsigned_repr -/(wbase Uptr) (cut_wbase_Uptr sz).
  rewrite (Z.mul_comm _ (CoqWord.word.modulus _)) mod_pq_mod_q // (Z.mul_comm _ p) Z_mod_plus.
  2: Psatz.lia.
  by rewrite mod_pq_mod_q //; apply/eqP/Zmod_divides; eauto.
Qed.

Lemma is_align_no_overflow ptr sz :
  is_align ptr sz → no_overflow ptr (wsize_size sz).
Proof.
  rewrite /no_overflow => /eqP ha; apply/ZleP.
  have hn := wsize_size_pos sz.
  have hnz : wsize_size sz ≠ 0%Z by Psatz.lia.
  move: (wunsigned ptr) (wunsigned_range ptr) ha => {ptr} ptr.
  rewrite (cut_wbase_Uptr sz); set a := CoqWord.word.modulus _.
  move: (wsize_size sz) hn hnz => n hn hnz hr /Zmod_divides [] // q ?; subst ptr.
  cut (q + 1 <= a)%Z; Psatz.nia.
Qed.

Lemma is_align8 (ptr:pointer) : is_align ptr U8.
Proof. by rewrite wsize8 /= Z.mod_1_r. Qed.

Instance A : alignment :=
  Alignment is_align8 is_align_array is_align_no_overflow.

End Align.

(** An example instance of the memory *)

Section RawMemoryI.

  Context (alloc: Mz.t unit).

  Record raw_mem : Type :=
    { data : Mz.t u8 }.

  Definition is_zalloc (m: Mz.t unit) (p:Z) : bool :=
    if Mz.get m p is Some _ then true else false.

  Definition is_alloc (m: raw_mem) (p:pointer) (ws: wsize) :=
    all (fun i => is_zalloc alloc (wunsigned (add p i))) (ziota 0 (wsize_size ws)).

  Lemma is_allocP m p ws :
    reflect (forall i, 0 <= i < wsize_size ws ->
               is_zalloc alloc (wunsigned (add p i)))
           (is_alloc m p ws).
  Proof.
    apply: equivP; first by apply allP.
    by split => h i hi; apply h; move: hi; rewrite in_ziota !zify Z.add_0_l.
  Qed.

  Definition raw_valid_pointer (m: raw_mem) (p:pointer) (ws: wsize) :=
    is_align p ws && is_alloc m p ws.

  Definition raw_valid m p ws := assert (raw_valid_pointer m p ws) ErrAddrInvalid.

  Lemma raw_sub_add m p s i t : raw_valid m p s = ok t -> 0 <= i < wsize_size s -> sub (add p i) p = i.
  Proof.
    rewrite /raw_valid => /assertP; rewrite /valid_pointer => /andP [].
    move=> /is_align_no_overflow; rewrite /no_overflow !zify => ha _ hi.
    have ? := wunsigned_range p; rewrite addE subE wunsigned_add; Psatz.lia.
  Qed.

  Definition uget (m: raw_mem) (p:pointer) := odflt 0%R (Mz.get m.(data) (wunsigned p)).

  Definition raw_uset (m: raw_mem) (p:pointer) (w:u8) :=
    {| data := Mz.set m.(data) (wunsigned p) w |}.

  Lemma raw_validw_uset m p v p' s : raw_valid (raw_uset m p v) p' s = raw_valid m p' s.
  Proof. done. Qed.

  Lemma raw_validrP m p s i t:
    raw_valid m p s = ok t ->
    0 <= i < wsize_size s ->
    raw_valid m (add p i) U8 = ok t.
  Proof.
    rewrite /raw_valid /raw_valid_pointer is_align8 /= andbC.
    by case: is_allocP => //= ha _ {}/ha; rewrite /is_alloc /= add_0 => ->; case: t.
  Qed.

  Lemma raw_validw_validr m p s i v t k:
    raw_valid m p s = ok t ->
    0 <= i < wsize_size s ->
    raw_valid (raw_uset m (add p i) v) k U8 = if add p i == k then ok t else raw_valid m k U8.
  Proof.
    rewrite /raw_valid /raw_valid_pointer is_align8 /=.
    case: andP => //= -[_ /is_allocP h] [<-] /h.
    by rewrite /is_alloc /= add_0 andbT; case:eqP => // <- ->.
  Qed.

  Lemma raw_setP m z1 z2 v:
    uget (raw_uset m z1 v) z2 = if z1 == z2 then v else uget m z2.
  Proof.
    by rewrite /uget /raw_uset /= Mz.setP (eqtype.inj_eq (@wunsigned_inj _)); case: eqP.
  Qed.

  Instance CM : coreMem Pointer raw_mem :=
    CoreMem raw_sub_add raw_validw_uset raw_validrP raw_validw_validr raw_setP.

  Definition raw_read_mem (m: raw_mem) (ptr: pointer) (ws: wsize) : exec (word ws) :=
    CoreMem.read m ptr ws.

  Definition raw_write_mem (m: raw_mem) (ptr:pointer) (ws:wsize) (v:word ws) :=
    CoreMem.write m ptr v.

  Instance RawMem : raw_memory raw_mem :=
    RawMemory raw_read_mem raw_write_mem raw_valid_pointer.

  Lemma readV (m: raw_mem) p s: reflect (exists v, raw_read_mem m p s = ok v) (raw_valid_pointer m p s).
  Proof.
    rewrite /raw_read_mem /CoreMem.read /= /raw_valid.
    by (case: raw_valid_pointer => /=; constructor) => [ | []//]; eauto.
  Qed.

  Lemma raw_writeV m p s (v:word s):
    reflect (exists m', raw_write_mem m p v = ok m') (raw_valid_pointer m p s).
  Proof.
    rewrite /raw_write_mem /CoreMem.write /= /raw_valid.
    by (case: raw_valid_pointer => /=; constructor) => [ | []//]; eauto.
  Qed.

  Lemma raw_read_mem_error m p s e: raw_read_mem m p s = Error e -> e = ErrAddrInvalid.
  Proof.
    by rewrite /raw_read_mem /CoreMem.read /= /raw_valid; case: raw_valid_pointer => [|[<-]].
  Qed.

  Lemma raw_write_read8 m m' p ws (v: word ws) k :
    raw_write_mem m p v = ok m' ->
    raw_read_mem m' k U8 =
      let i := wunsigned k - wunsigned p in
      if (0 <=? i) && (i <? wsize_size ws) then ok (LE.wread8 v i)
      else raw_read_mem m k U8.
  Proof. apply: CoreMem.write_read8. Qed.

  Lemma write_memE m m' p s (v:word s):
    raw_write_mem m p v = ok m' ->
    validw m p s = ok tt /\ m' = CoreMem.uwrite m p v.
  Proof.
    by rewrite /raw_write_mem /CoreMem.write /= /raw_valid /assert; case:ifP => //= _ [<-].
  Qed.

  Lemma raw_write_valid m m' p s (v:word s) p' s':
    raw_write_mem m p v = ok m' ->
    raw_valid_pointer m' p' s' = raw_valid_pointer m p' s'.
  Proof. done. Qed.

  Lemma raw_writeP_eq m m' p s (v :word s):
    raw_write_mem m p v = ok m' ->
    raw_read_mem m' p s = ok v.
  Proof.
    move=> hw; rewrite /raw_read_mem /CoreMem.read /= /raw_valid.
    rewrite (raw_write_valid _ _ hw).
    (case: (raw_writeV m p v); rewrite hw) => [[m1 _] /= | []]; last by eauto.
    by rewrite (CoreMem.writeP_eq hw) LE.decodeK.
  Qed.

  Lemma raw_writeP_neq m m' p s (v :word s) p' s':
    raw_write_mem m p v = ok m' ->
    disjoint_range p s p' s' ->
    raw_read_mem m' p' s' = raw_read_mem m p' s'.
  Proof.
    rewrite /raw_read_mem /CoreMem.read /= /raw_valid => hw [ /ZleP hno /ZleP hno' hd].
    rewrite (raw_write_valid p' s' hw); case: raw_valid_pointer => //=.
    rewrite (CoreMem.writeP_neq hw) // => i i' hi hi'.
    rewrite !addE => heq.
    have : wunsigned (p + wrepr U64 i)%R = wunsigned (p' + wrepr U64 i')%R by rewrite heq.
    have hp := wunsigned_range p; have hp' := wunsigned_range p'.
    rewrite !wunsigned_add; Psatz.lia.
  Qed.

  Lemma valid_align m p s: valid_pointer m p s -> is_align p s.
  Proof. by move=> /andP []. Qed.

  Lemma is_align_valid_pointer m p ws :
    is_align p ws ->
    (forall k, 0 <= k < wsize_size ws -> raw_valid_pointer m (add p k) U8) ->
    raw_valid_pointer m p ws.
  Proof.
    rewrite /raw_valid_pointer /is_alloc=> -> /= h.
    by apply /allP => i; rewrite in_ziota !zify => /h /and3P [] _; rewrite add_0.
  Qed.

End RawMemoryI.

Lemma raw_read_write_any_mem al1 m1 al1' m1' pr szr pw szw (vw:word szw) m2 m2':
  raw_valid_pointer al1 m1 pr szr ->
  raw_read_mem al1 m1 pr szr = raw_read_mem al1' m1' pr szr ->
  raw_write_mem al1 m1 pw vw = ok m2 ->
  raw_write_mem al1' m1' pw vw = ok m2' ->
  raw_read_mem al1 m2 pr szr = raw_read_mem al1' m2' pr szr.
Proof.
  move=> hv hr hw hw'; move: hr; rewrite /raw_read_mem /CoreMem.read /= /raw_valid.
  rewrite (raw_write_valid _ _ hw) (raw_write_valid _ _ hw') hv /=.
  case: raw_valid_pointer => //= h; have {h}/eqP/CoreMem.uread_decode h := ok_inj h; do 2 f_equal.
  apply /eqP /CoreMem.ureadP => i hin.
  by rewrite (CoreMem.write_uget _ hw) (CoreMem.write_uget _ hw') h.
Qed.

Instance RawMemCorrect al : raw_memory_spec Align.A (CM al) (RawMem al).
Proof.
  constructor.
  - exact: readV.
  - exact: raw_writeV.
  - exact: raw_read_mem_error.
  - done.
  - done.
  - exact: raw_write_read8.
  - exact: raw_writeP_eq.
  - exact: raw_writeP_neq.
  - exact: raw_write_valid.
  - exact: valid_align.
  - exact: is_align_valid_pointer.
  - move => m1; exact: (@raw_read_write_any_mem al m1 al).
Defined.

Module MemoryI : MemoryT.

  Instance A : alignment := Align.A.

  (** Total size of the stack *)
  Definition frames_size (frames: seq Z) :=
    foldr Z.add 0 frames.

  (** Frames are valid when:
    - sizes are positive
    - sizes are multiple of 32 (i.e., aligned for U256)
    - stack does not overflow
  *)
  Definition valid_frame (sz: Z) : bool :=
    (0 <=? sz) && (sz mod 32 == 0).

  Definition valid_frames (stk_root: pointer) (frames: seq Z) :=
    all valid_frame frames && (frames_size frames <=? wunsigned stk_root).

  Record mem_ := {
    as_raw_mem :> raw_mem;
    alloc : Mz.t unit;
    stk_root   : pointer; (* root of the stack *)
    stk_root_aligned : is_align stk_root U256;
    frames    : seq Z;        (* size of the frames on the stack *)
    framesP   : valid_frames stk_root frames;
    stk_allocP x : wunsigned stk_root - frames_size frames <= x < wunsigned stk_root → is_zalloc alloc x;
    stk_freeP x : 0 <= x < wunsigned stk_root - frames_size frames → is_zalloc alloc x = false;
  }.

  Arguments stk_allocP : clear implicits.
  Arguments stk_freeP : clear implicits.

  Definition mem := mem_.

  Definition valid_pointer (m: mem) p s : bool :=
    raw_valid_pointer m.(alloc) m p s.

  Definition read_mem (m: mem) p s : exec (word s) :=
    raw_read_mem m.(alloc) m p s.

  Definition write_mem (m: mem) p s (v: word s) : exec mem :=
      Let m' := raw_write_mem m.(alloc) m p v in
      ok {| as_raw_mem := m' ; stk_root_aligned := stk_root_aligned m ; framesP := framesP m ; stk_allocP := stk_allocP m ; stk_freeP := stk_freeP m |}.

  Instance RawMem : raw_memory mem :=
    {|
      memory_model.read_mem := read_mem
    ; memory_model.write_mem := write_mem
    ; memory_model.valid_pointer := valid_pointer
    |}.

  Definition uset (m: mem) p b : mem :=
    {| as_raw_mem := raw_uset m p b
     ; alloc := alloc m
     ; stk_root_aligned := stk_root_aligned m
     ; framesP := framesP m
     ; stk_allocP := stk_allocP m
     ; stk_freeP := stk_freeP m
    |}.

  Definition valid (m: mem) p ws : exec unit :=
    raw_valid (alloc m) m p ws.

  Lemma sub_add (m : mem) p s i t :
    valid m p s = ok t → 0 <= i < wsize_size s → sub (add p i) p = i.
  Proof. exact: raw_sub_add. Qed.

  Lemma validw_uset (m : mem) p v p' s :
    valid (uset m p v) p' s = valid m p' s.
  Proof. exact: raw_validw_uset. Qed.

  Lemma validrP (m : mem) p s i t :
    valid m p s = ok t → 0 <= i < wsize_size s → valid m (add p i) U8 = ok t.
  Proof. exact: raw_validrP. Qed.

  Lemma validw_validr (m : mem) p s i v t k :
    valid m p s = ok t → 0 <= i < wsize_size s →
    valid (uset m (add p i) v) k U8 = (if add p i == k then ok t else valid m k U8).
  Proof. exact: raw_validw_validr. Qed.

  Lemma setP (m : mem) z1 z2 v :
    uget (uset m z1 v) z2 = (if z1 == z2 then v else uget m z2).
  Proof. exact: raw_setP. Qed.

  Instance CM : coreMem Pointer mem :=
    @CoreMem pointer Pointer mem (λ m, uget m) uset valid valid sub_add validw_uset validrP validw_validr setP.

  Definition top_stack (m:mem) :=
    add m.(stk_root) (- frames_size m.(frames)).

  Definition set_alloc b (m:Mz.t unit) (ptr sz:Z) :=
    foldl (fun m k => if b then Mz.set m k tt else Mz.remove m k) m (ziota ptr sz).

  Lemma set_allocP b m p sz x :
    is_zalloc (set_alloc b m p sz) x =
      if (p <=? x) && (x <? p + sz) then b else is_zalloc m x.
  Proof.
    rewrite /set_alloc -in_ziota; elim: ziota m => //= i l hrec m.
    rewrite in_cons hrec orbC; case: ifP => //= ?.
    by rewrite /is_zalloc; case: {hrec} b;
      rewrite (Mz.setP, Mz.removeP) eq_sym; case: ifP.
  Qed.

  (** Stack blocks: association list of frame pointers to frame sizes *)
  Definition stack_blocks_rec stk_root frames :=
    foldr (λ s '(p, blk), let: q := add p (- s) in (q, (q, s) :: blk)) (stk_root, [::]) frames.

  Definition stack_blocks stk_root frames :=
    (stack_blocks_rec stk_root frames).2.

  Definition stack_frames (m: mem) : seq (pointer * Z) :=
    stack_blocks m.(stk_root) m.(frames).

  Lemma stack_blocks_rec_fst stk_root frames :
    (stack_blocks_rec stk_root frames).1 = add stk_root (- frames_size frames).
  Proof.
    elim: frames; first by rewrite add_0.
    move => f stk /=.
    case: (stack_blocks_rec _ _) => /= _ _ ->; rewrite addC; congr (add stk_root).
    Psatz.lia.
  Qed.

  Lemma stack_blocks_rec_snd_snd stk_root frames :
    map snd ((stack_blocks_rec stk_root frames).2) = frames.
  Proof.
    elim: frames => // f frames /=.
    by case: (stack_blocks_rec _ _) => /= _ ? <-.
  Qed.

  Lemma stack_blocks_rec_snd stk_root frames :
    if (stack_blocks_rec stk_root frames).2 is p_sz :: tl
    then let: (p, sz) := p_sz in p = add stk_root (- frames_size frames)
    else frames = [::].
  Proof.
    elim: frames => // f fr.
    have /= := (stack_blocks_rec_fst stk_root fr).
    case: (stack_blocks_rec _ _) => /= top [] //=.
    - move => -> -> /=; rewrite addC; congr (add _); Psatz.lia.
    case => _ _ _ -> _; rewrite addC; congr (add _); Psatz.lia.
  Qed.

  (** Allocation of a fresh block. *)
  Lemma alloc_stack_framesP (m: mem) s :
    valid_frame s && (s + frames_size m.(frames) <=? wunsigned m.(stk_root)) →
    valid_frames m.(stk_root) (s :: m.(frames)).
  Proof.
    case/andP => ok_s ofs; apply/andP; split; first (apply/andP; split).
    - exact: ok_s.
    - by have /andP[? _] := m.(framesP).
    exact: ofs.
  Qed.

  Lemma alloc_stack_stk_allocP (m: mem) s x :
    wunsigned (stk_root m) - frames_size (s :: frames m) <= x < wunsigned (stk_root m) →
    is_zalloc (set_alloc true (alloc m) (wunsigned m.(stk_root) - (s + frames_size m.(frames))) s) x.
  Proof.
    rewrite /= => range.
    rewrite set_allocP.
    case: ifPn; first done.
    rewrite !zify => not_range.
    apply: m.(stk_allocP); Psatz.lia.
  Qed.
  Arguments alloc_stack_stk_allocP [m s] x.

  Lemma alloc_stack_stk_freeP (m: mem) s x :
    valid_frame s && (s + frames_size m.(frames) <=? wunsigned m.(stk_root)) →
    0 <= x < wunsigned (stk_root m) - frames_size (s :: frames m) →
    is_zalloc (set_alloc true (alloc m) (wunsigned m.(stk_root) - (s + frames_size m.(frames))) s) x = false.
  Proof.
    case/andP=> /andP[]/lezP s_pos _ _ /= => range.
    rewrite set_allocP.
    case: ifPn; rewrite !zify; first Psatz.lia.
    move => nrange.
    apply: m.(stk_freeP); Psatz.lia.
  Qed.

  Definition alloc_stack (m: mem) (s: Z) : exec mem :=
    match Sumbool.sumbool_of_bool (valid_frame s && (s + frames_size m.(frames) <=? wunsigned m.(stk_root))) with
    | right _ => Error ErrStack
    | left C =>
      ok
        {| as_raw_mem := m;
           alloc := set_alloc true m.(alloc) (wunsigned m.(stk_root) - (s + frames_size m.(frames))) s;
           stk_root := m.(stk_root);
           stk_root_aligned := m.(stk_root_aligned);
           frames := s :: m.(frames);
           framesP := alloc_stack_framesP C;
           stk_allocP x := alloc_stack_stk_allocP x;
           stk_freeP x := alloc_stack_stk_freeP C;
        |}
    end.

  (** Free *)
  Lemma free_stack_framesP (m: mem) :
    valid_frames (stk_root m) (behead (frames m)).
  Proof.
    have /andP[h /lezP k] := m.(framesP).
    apply/andP; split.
    - by case: {k} (frames m) h => //= ? ? /andP[].
    rewrite zify.
    have [??] := wunsigned_range m.(stk_root).
    case: (frames m) h k => // a b /andP[] /andP[] /lezP a_pos _ _ /=.
    Psatz.lia.
  Qed.

  Lemma free_stack_stk_allocP (m: mem) x :
    wunsigned (stk_root m) - frames_size (behead (frames m)) <= x < wunsigned (stk_root m) →
    is_zalloc (set_alloc false (alloc m) (wunsigned (stk_root m) - frames_size (frames m)) (head 0 m.(frames))) x.
  Proof.
    move => range.
    have old_allocated := m.(stk_allocP) x.
    rewrite set_allocP; case: andP; rewrite !zify.
    - move: (frames m) range old_allocated => [] /= *; Psatz.lia.
    move: (frames m) (framesP m) range old_allocated => [] /=; first Psatz.lia.
    move: (stk_root m) => r f stk /andP[] /andP[] /andP[] /lezP f_pos _ _ _ range old_allocated nrange.
    apply: old_allocated.
    Psatz.lia.
  Qed.
  Arguments free_stack_stk_allocP : clear implicits.

  Lemma free_stack_stk_freeP (m: mem) x :
    0 <= x < wunsigned (stk_root m) - frames_size (behead (frames m)) →
    is_zalloc (set_alloc false (alloc m) (wunsigned (stk_root m) - frames_size (frames m)) (head 0 m.(frames))) x = false.
  Proof.
    move => range.
    have old_free := m.(stk_freeP) x.
    rewrite set_allocP; case: andP => //; rewrite !zify => nrange.
    apply: old_free.
    case: (frames m) range nrange => //= f stk; Psatz.lia.
  Qed.
  Arguments free_stack_stk_freeP : clear implicits.

  (* The “free” function ignores its size argument because its only valid value can be computed from the ghost data. *)
  Definition free_stack (m: mem) (_: Z) : mem :=
    let sz := head 0 m.(frames) in
    {| as_raw_mem := m;
       alloc := set_alloc false m.(alloc) (wunsigned m.(stk_root) - (frames_size m.(frames))) sz;
       stk_root := m.(stk_root);
       stk_root_aligned := m.(stk_root_aligned);
       frames := behead m.(frames);
       framesP := free_stack_framesP m;
       stk_allocP := free_stack_stk_allocP m;
       stk_freeP := free_stack_stk_freeP m;
    |}.

  (** Initial memory: empty with pre-allocated blocks.
    The stack is rooted at the higest aligned pointer below the lowest allocated address.
   *)
  Definition init_mem_alloc (s: seq (pointer * Z)) : Mz.t unit :=
    foldl (fun a pz => set_alloc true a (wunsigned pz.1) pz.2) (Mz.empty _) s.

  Definition all_above (s: seq (pointer * Z)) (stk: pointer) : bool :=
    all (λ '(p, _), wlt Unsigned stk p) s.

  Lemma init_mem_framesP stk :
    valid_frames stk [::].
  Proof. apply/lezP; exact: (proj1 (wunsigned_range _)). Qed.

  Lemma init_mem_stk_allocP stk_root s x :
    stk_root - 0 <= x < stk_root →
    is_zalloc (init_mem_alloc s) x.
  Proof. Psatz.lia. Qed.

  Lemma init_mem_stk_freeP_aux s stk m :
    all_above s stk →
    ∀ x,
      0 <= x <= wunsigned stk →
      is_zalloc (foldl (λ a pz, set_alloc true a (wunsigned pz.1) pz.2) m s) x = is_zalloc m x.
  Proof.
    rewrite /all_above.
    elim: s m => //= - [p z] s ih m /andP[] /ltzP ok_p {}/ih ih x x_range.
    rewrite (ih _ _ x_range) {ih} set_allocP /=.
    move: ok_p; rewrite -/(wunsigned stk) -/(wunsigned p) => ok_p.
    case: andP => //; rewrite !zify.
    Psatz.lia.
  Qed.

  Lemma init_mem_stk_freeP s stk x :
   all_above s stk →
    0 <= x < wunsigned stk - 0 →
    is_zalloc (init_mem_alloc s) x = false.
  Proof.
    move => all_above x_range.
    rewrite /init_mem_alloc (init_mem_stk_freeP_aux (Mz.empty _) all_above) //; Psatz.lia.
  Qed.
  Arguments init_mem_stk_freeP : clear implicits.

  Definition init_mem (s: seq (pointer * Z)) (stk: pointer) : exec mem :=
    match Sumbool.sumbool_of_bool (is_align stk U256) with
    | right _ => Error ErrStack
    | left stk_align =>
    match Sumbool.sumbool_of_bool (all_above s stk) with
    | right _ => Error ErrStack
    | left stk_below =>
      ok
        {| as_raw_mem := {| data := Mz.empty _ |};
           alloc := init_mem_alloc s;
           stk_root := stk;
           stk_root_aligned := stk_align;
           frames := [::];
           framesP := init_mem_framesP stk;
           stk_allocP := init_mem_stk_allocP s;
           stk_freeP p := init_mem_stk_freeP s stk p stk_below;
        |}
    end end.

  Instance M : memory mem :=
    Memory RawMem
           stk_root stack_frames alloc_stack free_stack init_mem.

  Lemma writeV (m : mem) p s (v: word s) :
    reflect (∃ m' : mem, write_mem m p v = ok m') (valid_pointer m p s).
  Proof.
    rewrite /valid_pointer /write_mem.
    case: (raw_writeV (alloc m) m p v) => h; constructor.
    - case: h => m' -> /=; eexists; reflexivity.
    case => m'; t_xrbindP => rm' k _; apply: h; rewrite k; eauto.
  Qed.

  Lemma read_mem_error (m: mem) p s e :
    read_mem m p s = Error e → e = ErrAddrInvalid.
  Proof. exact: raw_read_mem_error. Qed.

  Lemma writeP (m : mem) p s (v : word s) :
    write_mem m p v = CoreMem.write m p v.
  Proof.
    rewrite /write_mem /raw_write_mem /CoreMem.write /= /valid.
    case: raw_valid => //= _; congr ok.
    case: m => m al stk_root stk_root_ok fr fr_ok stk_alloc_ok stk_free_ok /=.
    rewrite /CoreMem.uwrite.
    elim: (ziota _ _) m => // i z ih m.
    by rewrite ih.
  Qed.

  Lemma write_read8 (m m' : mem) p  ws (v : word ws) k :
    write_mem m p v = ok m' →
    read_mem m' k U8 = (let i := wunsigned k - wunsigned p in
       if (0 <=? i) && (i <? wsize_size ws) then ok (LE.wread8 v i) else read_mem m k U8).
  Proof.
    rewrite /read_mem /write_mem; t_xrbindP => rm' ok_rm' <- {m'} /=.
    exact: raw_write_read8 k ok_rm'.
  Qed.

  Lemma writeP_eq (m m' : mem) p s (v : word s) :
    write_mem m p v = ok m' →
    read_mem m' p s = ok v.
  Proof.
    by rewrite /read_mem /write_mem; t_xrbindP => rm' /raw_writeP_eq h <-.
  Qed.

  Lemma writeP_neq (m m' : mem) p s (v : word s) p' s' :
   write_mem m p v = ok m' →
   disjoint_range p s p' s' →
   read_mem m' p' s' = read_mem m p' s'.
  Proof.
    rewrite /read_mem /write_mem; t_xrbindP => rm' h <- /=.
    exact: raw_writeP_neq h.
  Qed.

  Lemma write_valid (m m' : mem) p s (v : word s) p' s' :
    write_mem m p v = ok m' →
    valid_pointer m' p' s' = valid_pointer m p' s'.
  Proof.
    by rewrite /write_mem; t_xrbindP => rm' /raw_write_valid h <-.
  Qed.

  Lemma read_write_any_mem (m1 m1' : mem) pr szr pw szw (vw : word szw) (m2 m2' : mem) :
    valid_pointer m1 pr szr →
    read_mem m1 pr szr = read_mem m1' pr szr →
    write_mem m1 pw vw = ok m2 →
    write_mem m1' pw vw = ok m2' →
    read_mem m2 pr szr = read_mem m2' pr szr.
  Proof.
    rewrite /read_mem /write_mem => ok_pr eq_read.
    t_xrbindP => rm2 ok_rm2 <- {m2} rm2' ok_rm2' <- {m2'} /=.
    exact: (raw_read_write_any_mem ok_pr eq_read ok_rm2 ok_rm2').
  Qed.

  Instance RM : raw_memory_spec A CM as_raw_memory.
  Proof.
    constructor.
    - move => m; exact: readV.
    - move => m; exact: writeV.
    - exact: read_mem_error.
    - done.
    - exact: writeP.
    - exact: write_read8.
    - exact: writeP_eq.
    - exact: writeP_neq.
    - exact: write_valid.
    - move => m; exact: valid_align.
    - move => m; exact: is_align_valid_pointer.
    - exact: read_write_any_mem.
  Defined.

  Lemma top_stackE (m: mem) :
    memory_model.top_stack m = top_stack m.
  Proof.
    rewrite /memory_model.top_stack /= /stack_frames /top_stack /stack_blocks.
    have := stack_blocks_rec_snd (stk_root m) (frames m).
    case: (stack_blocks_rec _ _) => /= _ [] //=; last by case.
    by move => ->; rewrite add_0.
  Qed.

  Lemma top_stack_write_mem m p s (v: word s) m' :
    write_mem m p v = ok m' →
    top_stack m = top_stack m'.
  Proof. by rewrite /write_mem; t_xrbindP => ? _ <-. Qed.

  Lemma write_mem_stable m m' p s (v:word s) :
    write_mem m p v = ok m' -> stack_stable m m'.
  Proof. by rewrite /write_mem; t_xrbindP => ? _ <-. Qed.

  (** Allocation *)
  Lemma valid_frames_size_pos frames :
    all valid_frame frames →
    0 <= frames_size frames.
  Proof.
    elim: frames; first reflexivity.
    move => /= b f ih /andP[] /andP[] /lezP b_pos _ {}/ih.
    Psatz.lia.
  Qed.

  Corollary frames_size_pos (m: mem) :
    0 <= frames_size m.(frames).
  Proof.
    have /andP[h _] := m.(framesP).
    exact: valid_frames_size_pos.
  Qed.
  Arguments frames_size_pos : clear implicits.

  Lemma frames_size_align (m: mem) :
    frames_size m.(frames) mod 32 == 0.
  Proof.
    have /andP[h _] := m.(framesP).
    apply/aligned_factor => //.
    elim: {m} (frames m) h; first by exists 0.
    move => b f ih /andP[] /andP[] /lezP b_pos /aligned_factor - /(_ erefl) [a ab] {}/ih [c fc].
    change (frames_size (b :: f)) with (b + frames_size f).
    exists (a + c). Psatz.lia.
  Qed.

  Lemma ass_mod (m m': mem) sz: alloc_stack m sz = ok m' -> wunsigned (top_stack m') + sz <= wbase Uptr.
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-] /=.
    rewrite /top_stack /=.
    case/andP: h => /andP[] /lezP ok_sz _ /lezP ovf.
    have fs_pos := frames_size_pos m.
    have r_range := wunsigned_range m.(stk_root).
    rewrite wunsigned_add; Psatz.lia.
  Qed.

  Lemma ass_valid m sz m' :
    alloc_stack m sz = ok m' →
    ∀ p s,
    valid_pointer m' p s =
    valid_pointer m p s || between (top_stack m') sz p s && is_align p s.
  Proof.
    rewrite /alloc_stack /valid_pointer /raw_valid_pointer; case: Sumbool.sumbool_of_bool => // h [<-] p s.
    case ok_p_s: (is_align _ _); last by rewrite andbF.
    rewrite /= /is_alloc /top_stack /= andbT.
    case/andP: h => /andP[] /lezP sz_pos sz_align /lezP no_ovf.
    symmetry.
    case: allP => /=.
    - move => old; symmetry.
      apply/allP => i {}/old old.
      rewrite set_allocP old.
      by case: ifP.
    case/allP/allPn => j j_range /negbTE j_not_allocated.
    have b_pos := wunsigned_range m.(stk_root).
    have f_pos := frames_size_pos m.
    rewrite /between wunsigned_add; last Psatz.lia.
    case/aligned_factor: m.(stk_root_aligned); first done.
    move: (wunsigned m.(stk_root)) (frames_size m.(frames)) b_pos f_pos no_ovf (frames_size_align m) =>
      b f b_pos f_pos no_ovf f_align low ?; subst b.
    symmetry; rewrite /between; case: andP; rewrite !zify => btw; apply/allP.
    - move => /= i; rewrite in_ziota !zify => i_range; rewrite set_allocP.
      rewrite wunsigned_add; last Psatz.lia.
      case: andP => //; rewrite !zify; Psatz.lia.
    move => /(_ _ j_range); rewrite set_allocP {}j_not_allocated.
    case: andP => //; rewrite !zify.
    move: j_range; rewrite in_ziota !zify => j_range.
    have := is_align_no_overflow ok_p_s.
    rewrite /no_overflow !zify => ovf.
    have p_pos := wunsigned_range p.
    rewrite wunsigned_add; last Psatz.lia.
    move => pj_range _; apply: btw.
    case/aligned_factor: f_align => // stack ?; subst f.
    case/aligned_factor: sz_align => // frame ?; subst sz.
    have := wsize_size_le (wsize_ge_U256 s).
    change (wsize_size U256) with 32 in *.
    case => n ws.
    move: sz_pos b_pos f_pos pj_range; rewrite {}ws => sz_pos b_pos f_pos pj_range.
    have wsnz : wsize_size s != 0 by case: (s).
    have p_align := aligned_factor _ wsnz ok_p_s.
    move: {p ok_p_s} (wunsigned p) p_align ovf p_pos pj_range => _ [] p ->.
    move: sz_pos b_pos f_pos.
    move: {s wsnz} (wsize_size s) j_range => w j_range sz_pos b_pos f_pos ovf p_pos pj_range.
    rewrite Z.add_0_l in j_range.
    have jwz := Zdiv_small _ _ j_range.
    suff : n * (low - (frame + stack)) <= p + j / w < n * (low - (frame + stack) + frame);
    Psatz.nia.
  Qed.

  Lemma ass_read_old m sz m' :
    alloc_stack m sz = ok m' →
    ∀ p s,
    valid_pointer m p s →
    read_mem m p s = read_mem m' p s.
  Proof.
    move => ok_m' p s ok_m_p_s.
    have : valid_pointer m' p s.
      by rewrite (ass_valid ok_m') ok_m_p_s.
    move: ok_m'.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-].
    by rewrite /read_mem /raw_read_mem /CoreMem.read /= /CoreMem.uread /= /raw_valid /valid_pointer -/(valid_pointer m p s) ok_m_p_s /= => ->.
  Qed.

  Lemma ass_align m sz m' :
    alloc_stack m sz = ok m' →
    ∀ ofs s,
      is_align (top_stack m' + wrepr U64 ofs) s = is_align (wrepr U64 ofs) s.
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-].
    rewrite /is_align /top_stack /= => ofs s.
    case/andP: h => /andP[] /lezP sz_pos.
    have := frames_size_align m.
    have := m.(stk_root_aligned).
    rewrite /is_align /=.
    have := wsize_size_le (wsize_ge_U256 s).
    change (wsize_size U256) with 32 => - [] n ws.
    have ws_pos := wsize_size_pos s.
    have n_pos : 0 < n by Psatz.nia.
    have ns_nz : n * wsize_size s ≠ 0 by Psatz.lia.
    move: ws => -> /eqP rt_align /eqP fs_align /eqP /Z.mod_opp_l_z - /(_ ns_nz) sz_align _.

    rewrite /add wunsigned_repr /=.
    rewrite /wunsigned /=.
    rewrite !word.addwE.
    rewrite !word.mkwordK.
    rewrite word.urepr_word /=.
    change (word.modulus nat63.+1) with (wbase U64).
    rewrite (cut_wbase_Uptr s) (Z.mul_comm (wsize_size s)).
    rewrite Z.add_mod_idemp_l //.
    rewrite !mod_pq_mod_q //.
    rewrite Z.add_mod //.
    rewrite !mod_pq_mod_q //.
    rewrite (Z.add_mod (word.toword m.(stk_root))) //.
    replace (word.toword m.(stk_root) mod wsize_size s) with 0; last first.
    - etransitivity. 2: apply: (@mod_pq_mod_q _ n) => //.
      rewrite /wunsigned /word.urepr /= in rt_align.
      by rewrite rt_align.
    rewrite !mod_pq_mod_q //=.
    rewrite Z.opp_add_distr (Z.add_mod (- sz)) //.
    rewrite -(@mod_pq_mod_q (-sz) n) // sz_align /=.
    rewrite Z.mod_opp_l_z //.
    - by rewrite /= Z.mod_mod.
    symmetry. etransitivity. 2: apply: (@mod_pq_mod_q _ n) => //.
    by rewrite fs_align.
  Qed.

  Lemma ass_fresh m sz m' :
    alloc_stack m sz = ok m' →
    ∀ p s,
      valid_pointer m p s →
      (wunsigned p + wsize_size s <= wunsigned (top_stack m') ∨ wunsigned (top_stack m') + sz <= wunsigned p).
  Proof.
    move => X; have := m.(stk_freeP); move: X.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-] /= stk_fresh p s /andP[] p_align p_alloc.
    rewrite /top_stack /=.
    right. apply/lezP; case: lezP => // /Z.nle_gt X.
    rewrite -(stk_fresh (wunsigned p)).
    - by move/allP: p_alloc => /(_ 0); rewrite in_ziota /= (proj2 (Z.ltb_lt _ _) (wsize_size_pos s)) add_0 => /(_ erefl).
    split. apply wunsigned_range.
    rewrite wunsigned_add in X. Psatz.lia.
    case/andP: h => /andP[] /lezP sz_pos _ /lezP.
    have := wunsigned_range (stk_root m).
    have := frames_size_pos m.
    Psatz.lia.
  Qed.

  Lemma ass_frames m sz m' :
    alloc_stack m sz = ok m' →
    stack_frames m' = (top_stack m', sz) :: stack_frames m.
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-] /=.
    rewrite /stack_frames /top_stack /=.
    rewrite {1}/stack_blocks /=.
    case heq: (stack_blocks_rec _ _) => [p blk].
    rewrite /stack_blocks heq /=.
    congr ((_, _) :: _).
    have := stack_blocks_rec_fst (stk_root m) (frames m).
    rewrite heq /= => ->; rewrite addC; congr add.
    Psatz.lia.
  Qed.

  Lemma alloc_stackP m m' sz :
    alloc_stack m sz = ok m' -> alloc_stack_spec m sz m'.
  Proof.
    move => o.
    split; rewrite ?top_stackE.
    - exact: ass_mod o.
    - exact: ass_read_old o.
    - exact: ass_valid o.
    - exact: ass_align o.
    - exact: ass_fresh o.
    exact: ass_frames o.
  Qed.

  Lemma first_frameE m sz :
    omap snd (ohead (stack_frames m)) = Some sz →
    head 0 (frames m) = sz.
  Proof.
    rewrite /stack_frames /stack_blocks.
    have := stack_blocks_rec_snd_snd (stk_root m) (frames m).
    by case: (stack_blocks_rec _ _) => /= _ [] //= [] /= _ p q <- /Some_inj.
  Qed.

  Lemma fss_valid m sz p s :
    omap snd (ohead (stack_frames m)) = Some sz →
    valid_pointer (free_stack m sz) p s ↔ valid_pointer m p s ∧ disjoint_zrange (top_stack m) sz p (wsize_size s).
  Proof.
    have /andP[ ok_frames /lezP no_underflow ] := framesP m.
    move => /first_frameE o.
    rewrite /valid_pointer /raw_valid_pointer /free_stack /is_alloc /=.
    case: eqP; last by move => _ /=; split => // - [].
    move => aligned_p /=; symmetry.
    case: allP.
    + move => old_allocated; split.
      - case => _ disj; apply/allP => /= i /dup[] {}/old_allocated old_allocated.
        rewrite in_ziota => /andP[] /lezP i_pos /ltzP /= i_bound.
        rewrite set_allocP; case: andP => // - []; rewrite !zify => X Y.
        case: disj; rewrite /top_stack => /lezP noo /lezP noo'.
        have p_range := wunsigned_range p.
        have pi_range : 0 <= wunsigned (add p i) < wbase U64 by exact: wunsigned_range.
        rewrite wunsigned_add; last by Psatz.lia.
        rewrite wunsigned_add in X; last by Psatz.lia.
        rewrite wunsigned_add in Y; last by Psatz.lia.
        Psatz.lia.
      move/allP => new_allocated.
      apply: (conj erefl).
      have root_range := wunsigned_range (stk_root m).
      have fs_pos := frames_size_pos m.
      split.
      - rewrite /top_stack /no_overflow wunsigned_add; last Psatz.lia.
        rewrite zify -o.
        case: (frames m) fs_pos ok_frames => [ | f fr ] /=; first Psatz.lia.
        move => _ /andP[] _ /valid_frames_size_pos; Psatz.lia.
      - rewrite /no_overflow zify.
        case/eqP/aligned_factor: aligned_p (wunsigned_range p) => // q.
        rewrite (cut_wbase_Uptr s).
        have ? := wsize_size_pos s.
        move: (word.modulus _) => n -> ?.
        suff : 0 <= q < n; Psatz.nia.
      rewrite o in new_allocated.
      rewrite /top_stack wunsigned_add; last Psatz.lia.
      have range_0 : 0 \in ziota 0 (wsize_size s) by rewrite in_ziota !zify.
      move: old_allocated => /(_ 0 range_0) old_allocated.
      move: new_allocated => /(_ _ range_0).
      rewrite set_allocP {}old_allocated -Bool.if_negb -Bool.orb_lazy_alt orbF negb_and add_0 -Z.ltb_antisym -Z.leb_antisym.
      case: Z.leb_spec0; first by left.
      rewrite orbF => K.
      case: Z.ltb_spec0 => // L _; right.
      have sz_align : sz mod 32 == 0.
      { move: ok_frames o; case: (frames m) => /=; first by move => _ <-.
        move => a ? /andP[] /andP [] _; congruence. }
      case/eqP/aligned_factor: aligned_p (wunsigned_range p) L K => // q ->.
      have := stk_root_aligned m.
      rewrite /is_align /=.
      have := wsize_size_le (wsize_ge_U256 s).
      change (wsize_size U256) with 32 => - [] n ws.
      move: (frames_size_align m).
      case/aligned_factor => // j -> /aligned_factor[] // k ->.
      move: ws.
      have : wsize_size s <= 32 by case: (s).
      have := wsize_size_pos s.
      move: (wsize_size s) => x x_pos x_le_32 nx qx_range L K.
      suff : 0 <= n ∧ 0 <= q;
      Psatz.nia.
    move => old_not_allocated; split; first by case.
    move/allP => new_allocated; elim: old_not_allocated => /= i /dup[] {}/new_allocated.
    by rewrite set_allocP; case: andP.
  Qed.

  Lemma fss_read_old m sz p s :
    omap snd (ohead (stack_frames m)) = Some sz →
    valid_pointer (free_stack m sz) p s →
    read_mem m p s = read_mem (free_stack m sz) p s.
  Proof.
    move => ok_sz /dup[] ok_p_s' /fss_valid - /(_ ok_sz) [ok_p_s _].
    rewrite /read_mem /raw_read_mem /CoreMem.read /= /raw_valid.
    by move: ok_p_s' ok_p_s; rewrite /valid_pointer => -> ->.
  Qed.

  Lemma free_stackP m sz :
    omap snd (ohead (stack_frames m)) = Some sz ->
    free_stack_spec m sz (free_stack m sz).
  Proof.
    move => o; split => *.
    - exact: fss_read_old.
    - rewrite top_stackE; exact: fss_valid.
    rewrite /memory_model.frames /= /stack_frames /= /stack_blocks.
    case: (frames m) => //= f fr.
    by case: (stack_blocks_rec _ _).
  Qed.

  (** Refinement to a low memory. *)

  Definition low_mem := (Mz.t unit * raw_mem)%type.

  Instance LM : raw_memory low_mem :=
    {| memory_model.read_mem am := raw_read_mem am.1 am.2
     ; memory_model.write_mem am p s v := Let m' := raw_write_mem am.1 am.2 p v in ok (am.1, m')
     ; memory_model.valid_pointer am := raw_valid_pointer am.1 am.2
    |}.

  Instance LCM : coreMem Pointer low_mem.
  Proof.
    refine
      {| memory_model.uget m := uget m.2
       ; memory_model.uset m p v := (m.1, raw_uset m.2 p v)
       ; memory_model.validr m := raw_valid m.1 m.2
       ; memory_model.validw m := raw_valid m.1 m.2
      |}.
   - move => m; exact: raw_sub_add.
   - move => m; exact: raw_validw_uset.
   - move => m; exact: raw_validrP.
   - move => m; exact: raw_validw_validr.
   - move => m; exact: raw_setP.
  Defined.

  Instance LMS : raw_memory_spec A LCM LM.
  Proof.
    constructor.
    - move => m; exact: readV.
    - move => m p s v; rewrite /memory_model.write_mem /memory_model.valid_pointer /=.
      case: (raw_writeV m.1 m.2 p v) => h; constructor.
      + by case: h => m' ->; eexists.
      by case; t_xrbindP => ????; subst; apply: h; eexists; eassumption.
    - move => m; exact: raw_read_mem_error.
    - done.
    - move => m p s v; rewrite /memory_model.write_mem /= /raw_write_mem /CoreMem.write /=.
      case: raw_valid => //= _.
      congr ok; case: m => /= al.
      rewrite /CoreMem.uwrite /=.
      elim: (ziota _ _) => //=.
    - rewrite /memory_model.write_mem /=; t_xrbindP => ??????? /raw_write_read8 h ?; subst; exact: h.
    - by rewrite /memory_model.write_mem /memory_model.read_mem /=; t_xrbindP => ?????? /raw_writeP_eq <- <-.
    - rewrite /memory_model.write_mem /memory_model.read_mem /=; t_xrbindP => ???????? /raw_writeP_neq h <-; exact: h.
    - rewrite /memory_model.write_mem /=; t_xrbindP => ???????? /raw_write_valid h <-; exact: h.
    - move => m; exact: valid_align.
    - move => m; exact: is_align_valid_pointer.
    - rewrite /memory_model.write_mem /memory_model.read_mem /=; t_xrbindP => ?????????  /raw_read_write_any_mem h /h {h} h ? /h {h} h <- ?? <-; exact: h.
  Defined.

  Definition eqalloc (a b: Mz.t unit) : Prop :=
    is_zalloc a =1 is_zalloc b.

  Remark eqalloc_trans y x z : eqalloc x y → eqalloc y z → eqalloc x z.
  Proof. by move => a ? ?; rewrite a. Qed.

  Lemma is_alloc_m a b {m p ws} : eqalloc a b → is_alloc a m p ws = is_alloc b m p ws.
  Proof. by move => eq_a_b; apply/eq_all. Qed.

  Definition eqmem (a: mem) (stack: pointer) (b: low_mem) : Prop :=
    [/\ stack = add (stk_root a) (- frames_size (frames a)), eqalloc b.1 (set_alloc true (alloc a) 0 (wunsigned stack)) & b.2 = as_raw_mem a ].

  Lemma is_alloc_set_alloc al m p s ptr sz :
    is_alloc al m p s →
    is_alloc (set_alloc true al ptr sz) m p s.
  Proof.
    move/is_allocP => h; apply/is_allocP => i i_range; rewrite set_allocP.
    case: ifP => // _; exact: h.
  Qed.

  Instance L : refinement M LM eqmem.
  Proof.
    split.
    - rewrite /memory_model.read_mem /= /read_mem => a stack [] al _ [/= -> ok_al ->] p s v.
      rewrite /raw_read_mem /CoreMem.read /= /raw_valid /raw_valid_pointer; t_xrbindP => /= _ /assertP /andP[] -> ok_p -> /=.
      by rewrite (is_alloc_m ok_al) (is_alloc_set_alloc _ _ ok_p).
    - rewrite /memory_model.write_mem /= /write_mem => a stack [] al _ [/= -> ok_al ->] p s v ?; t_xrbindP => a' ok_a' <-.
      move: ok_a'.
      rewrite /raw_write_mem /CoreMem.write /= /raw_valid /raw_valid_pointer; t_xrbindP => /= _ /assertP /andP[] -> ok_p <-.
      rewrite (is_alloc_m ok_al) (is_alloc_set_alloc _ _ ok_p).
      by eexists; first reflexivity.
    rewrite /eqmem /= /alloc_stack => a stack [] al _ [/= -> ok_al ->] sz a'; rewrite addC.
    case: Sumbool.sumbool_of_bool => // ok_check /(@ok_inj _ _ _ _) <- {a'} /=.
    split; last reflexivity.
    - congr (add a.(stk_root)); Psatz.lia.
    case/andP: ok_check => /andP[] /lezP sz_pos sz_align /lezP no_overflow.
    apply: (eqalloc_trans ok_al) => p; rewrite !set_allocP.
    have rt_range := wunsigned_range a.(stk_root).
    have fr_pos := frames_size_pos a.
    do 2 (rewrite wunsigned_add; last by Psatz.lia).
    move: (wunsigned a.(stk_root)) no_overflow rt_range => r no_overflow r_range /=.
    case: andP.
    - case => /dup[] /lezP p_pos -> /= /ltzP p_bounded.
      case: ifPn => // /ltzP ?.
      case: ifPn => //. rewrite negb_and => /orP [].
      + move => /lezP; Psatz.lia.
      move => /ltzP; Psatz.lia.
    rewrite -(rwP lezP) -(rwP ltzP) => ?.
    case: andP; rewrite -(rwP lezP) -(rwP ltzP); first Psatz.lia.
    case: andP => //; rewrite -(rwP lezP) -(rwP ltzP).
    Psatz.lia.
  Qed.

End MemoryI.
