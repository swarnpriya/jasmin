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
  | Mconst : word -> mexpr
  | Mbool : bool -> mexpr
  | Madd : mexpr -> mexpr -> mexpr
  | Mand : mexpr -> mexpr -> mexpr
  | Mget : var -> mexpr -> mexpr.

Variant mrval : Type :=
    MRvar : var -> mrval
  | MRaset : var -> mexpr -> mrval.

Variant minstr : Type :=
  MCassgn : mrval -> mexpr -> minstr.

Notation mcmd := (seq minstr).

Definition mon_arr_var A (s:svmap) (x:var) (f:forall n, FArray.array word -> A) :=
  match vtype x as t return ssem_t t -> A with
  | sarr n => f n
  | _ => fun _ => f xH (FArray.cnst (n2w 0))
  end  (s.[ x ]%vmap).

Notation "'MLet' ( n , t ) ':=' s '.[' x ']' 'in' body" :=
  (@mon_arr_var _ s x (fun n (t:FArray.array word) => body)) (at level 25, s at level 0).

Fixpoint msem_mexpr (s: svmap) (e: mexpr) : exec svalue :=
  match e with
  | Mvar v => ok (sget_var s v)
  | Mbool b => ok (SVbool b)
  | Mconst z => ok (SVword z)
  | Madd e1 e2 =>
    Let x1 := msem_mexpr s e1 in
    Let x2 := msem_mexpr s e2 in
    Let i1 := sto_word x1 in
    Let i2 := sto_word x2 in
    ok (SVword (I64.add i1 i2))
  | Mand e1 e2 =>
    Let x1 := msem_mexpr s e1 in
    Let x2 := msem_mexpr s e2 in
    Let i1 := sto_bool x1 in
    Let i2 := sto_bool x2 in
    ok (SVbool (andb i1 i2))
  | Mget x e =>
    MLet (n,t) := s.[x] in
    Let i := msem_mexpr s e >>= sto_word in
    ok (SVword (FArray.get t i))
  end.

Definition mwrite_rval (l: mrval) (v: svalue) (s: svmap) : exec svmap :=
  match l with
  | MRvar x => sset_var s x v
  | MRaset x i =>
    MLet (n,t) := s.[x] in
    Let i := msem_mexpr s i >>= sto_word in
    Let v := sto_word v in
    let t := FArray.set t i v in
    sset_var s x (@to_sval (sarr n) t)
  end.

Inductive msem : svmap -> mcmd -> svmap -> Prop :=
    MEskip : forall s : svmap, msem s [::] s
  | MEseq : forall (s1 s2 s3 : svmap) (i : minstr) (c : mcmd),
           msem_I s1 i s2 -> msem s2 c s3 -> msem s1 (i :: c) s3
  with msem_I : svmap -> minstr -> svmap -> Prop :=
  | MEassgn : forall (s1 s2 : svmap) (r : mrval) (e : mexpr),
    Let v := msem_mexpr s1 e in mwrite_rval r v s1 = ok s2 ->
    msem_I s1 (MCassgn r e) s2.

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
  | MCassgn r e => ∃ v, msem_mexpr s e = ok v ∧ mwrite_rval r v s = ok s'
  end.
Proof.
  by case=> s1 s2 x e H; case: (bindW H); eauto.
Qed.

Lemma msem_cat_inv s c1 c2 s': msem s (c1 ++ c2) s' -> exists s1, msem s c1 s1 /\ msem s1 c2 s'.
Proof.
elim: c1 s=> [|a l IH] s /=.
+ exists s; split=> //; exact: MEskip.
+ move=> /msem_inv [s1 [Hi Hc]].
  move: (IH _ Hc)=> [s2 [Hc1 Hc2]].
  exists s2; split=> //.
  apply: MEseq; [exact: Hi|exact: Hc1].
Qed.

Lemma msem_I_det s s1 s2 i: msem_I s i s1 -> msem_I s i s2 -> s1 = s2.
Proof.
  case: i=> r e.
  move=> /msem_I_inv [v1 [Hv1 Hr1]].
  move=> /msem_I_inv [v2 []].
  rewrite {}Hv1 => -[] <-.
  by rewrite Hr1=> -[] <-.
Qed.

(*
 * Define the trace of instructions
 *)

Module Trace.
Definition trace := seq (exec svalue).

Fixpoint trace_expr (s: svmap) (e: mexpr) : trace :=
  match e with
  | Mvar v => [::]
  | Mbool b => [::]
  | Mconst z => [::]
  | Madd e1 e2 => (trace_expr s e1) ++ (trace_expr s e2)
  | Mand e1 e2 => (trace_expr s e1) ++ (trace_expr s e2)
  | Mget x e => [:: msem_mexpr s e]
  end.

Definition trace_instr (s: svmap) (c: minstr) : trace :=
  match c with
  | MCassgn _ e => trace_expr s e
  end.
End Trace.

Import Trace.

(*
 * Definition 1/4: use a fixpoint
 *)
Module Leakage_Fix.
Fixpoint leakage_fix (s: svmap) (c: mcmd) (s': svmap) (p: msem s c s') {struct p} : seq (exec svalue).
  refine
  (match c as c0 return c = c0 -> seq (exec svalue) with
  | [::] => fun _ => [::]
  | i :: c' => fun (Hc: c = i::c') =>
    (trace_instr s i) ++
    (match i as i0 return i = i0 -> seq (exec svalue) with
    | MCassgn r e => fun (Hi: i = MCassgn r e) =>
      match msem_mexpr s e as e0 return msem_mexpr s e = e0 -> seq (exec svalue) with
      | Ok v => fun (He : msem_mexpr s e = ok v) =>
        match mwrite_rval r v s as s0 return mwrite_rval r v s = s0 -> seq (exec svalue) with
        | Ok s1 => fun (Hs: mwrite_rval r v s = ok s1) => (leakage_fix s1 c' s' _)
        | Error err => _
        end (erefl _)
      | Error err => _
      end (erefl _)
    end (erefl _))
  end (erefl _)).
  + case: p Hc He Hs;first by done.
    move=> s0 s2 s3 i0 c0 H1 H2 H.
    move: H H1 H2 => [-> ->] H1.
    case: H1 Hi => ???? H Heq.
    move: Heq H=> [-> ->] H1 H2 H3 H4.
    move: H1;rewrite H3 /= H4 => -[->];exact H2.
  + by move=> _;exact [::].
  by move=> _;exact [::].
Defined.
End Leakage_Fix.

(*
 * Definition 2/4: put the trace in Prop to make it simpler
 *)
Module Leakage_Ex.
Variant trace : Prop :=
  ExT : seq (exec svalue) -> trace.

Definition trace_cat t1 t2 :=
  match t1 with
  | ExT s1 =>
    match t2 with
    | ExT s2 => ExT (s1 ++ s2)
    end
  end.

Definition trace_cons l t :=
  match t with
  | ExT s => ExT (l :: s)
  end.

Definition leakage (s: svmap) (c: mcmd) (s': svmap) (p: msem s c s') : trace.
Proof.
  elim: c s p=> [s H|i c H s].
  exact (ExT [::]).
  move => /msem_inv [s1 [Hi /H [] q]].
  exact (ExT ((trace_instr s i) ++ q)).
Defined.

Lemma leakage_irr (s: svmap) (c: mcmd) (s': svmap) (p: msem s c s') (p': msem s c s'):
  leakage p = leakage p'.
Proof.
  elim: c s p p'=> [p p'|a l IH s p p'].
  by rewrite /leakage /=.
  rewrite /leakage /=.
  move: p=> /msem_inv [s1 [Hi1 Hc1]].
  move: p'=> /msem_inv [s2 [Hi2 Hc2]].
  move: (msem_I_det Hi1 Hi2)=> H.
  move: Hi1 Hi2 Hc1 Hc2.
  case: _ / H=> _ Hi Hc1 Hc2.
  move: (IH _ Hc1 Hc2).
  rewrite /leakage /==> -> //.
Qed.

Lemma leakage_cat s c1 c2 s' (p: msem s (c1 ++ c2) s'):
  exists s1 p' p'',
  @leakage s (c1 ++ c2) s' p = trace_cat (@leakage s c1 s1 p') (@leakage s1 c2 s' p'').
Proof.
  move: (msem_cat_inv p)=> [s1 [p' p'']].
  exists s1; exists p'; exists p''.
  elim: c1 s p p'=> /= [s p p'|a l IH s p p'].
  move: p'=> /msem_inv H.
  move: p p''.
  case: _ / H=> p p''.
  rewrite (leakage_irr p p'') //.
  case: (leakage p'')=> //.
  move: p=> /msem_inv [s2 [Hs2 Hs2']].
  move: p'=> /msem_inv [s3 [Hs3 Hs3']].
  move: (msem_I_det Hs2 Hs3)=> Hs.
  move: Hs2 Hs2' Hs3 Hs3'.
  case: _ / Hs=> _ Hs2' _ Hs3'.
  rewrite (IH _ Hs2' Hs3').
  case: (leakage Hs3')=> // t.
  rewrite /trace_cat /=.
  case: (leakage p'')=> // v.
  by rewrite catA.
Qed.
End Leakage_Ex.

(*
 * Definition 3/4: instrumented big step semantics
 *)
Module Leakage_Instr.
  Inductive mtsem : svmap -> mcmd -> Trace.trace -> svmap -> Prop :=
    MTEskip : forall s : svmap, mtsem s [::] [::] s
  | MTEseq : forall (s1 s2 s3 : svmap) (i : minstr) (c : mcmd) (t: trace),
           mtsem_I s1 i s2 -> mtsem s2 c t s3 -> mtsem s1 (i :: c) ((trace_instr s1 i) ++ t) s3
  with mtsem_I : svmap -> minstr -> svmap -> Prop :=
  | MTEassgn : forall (s1 s2 : svmap) (r : mrval) (e : mexpr),
    Let v := msem_mexpr s1 e in mwrite_rval r v s1 = ok s2 ->
    mtsem_I s1 (MCassgn r e) s2.

  Lemma mtsem_inv s c t s' :
    mtsem s c t s' →
    match c with
    | [::] => s' = s /\ t = [::]
    | i :: c' => ∃ s1 t1, mtsem_I s i s1 ∧ mtsem s1 c' t1 s' /\ t = (trace_instr s i) ++ t1
  end.
  Proof. by case; eauto. Qed.

  Lemma mtsem_I_inv s i s' :
    mtsem_I s i s' →
    match i with
    | MCassgn r e => ∃ v, msem_mexpr s e = ok v ∧ mwrite_rval r v s = ok s'
    end.
  Proof.
    by case=> s1 s2 x e H; case: (bindW H); eauto.
  Qed.

  Lemma mtsem_cat_inv s c1 c2 s' t: mtsem s (c1 ++ c2) t s' ->
    exists s1 t1 t2, mtsem s c1 t1 s1 /\ mtsem s1 c2 t2 s' /\ t = t1 ++ t2.
  Proof.
  elim: c1 t s=> [|a l IH] t s /=.
  + exists s; exists [::]; exists t; split=> //; exact: MTEskip.
  + move=> /mtsem_inv [s1 [t1 [Hi [Hc Ht]]]].
    move: (IH _ _ Hc)=> [s2 [t2 [t3 [Hc1 [Hc2 Ht2]]]]].
    exists s2; exists (trace_instr s a ++ t2); exists t3; split.
    apply: MTEseq; [exact: Hi|exact: Hc1].
    split=> //.
    by rewrite Ht Ht2 catA.
  Qed.
End Leakage_Instr.

(*
 * Definition 4/4: using small step semantics (two possibilities?)
 *)
Module Leakage_Smallstep.
  (* TODO *)
End Leakage_Smallstep.

(*
 * Define the constant time property (here, associated with Leakage_Ex)
 *)

Definition seq_on (s : Sv.t) (vm1 vm2 : svmap) :=
  forall x, Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Section ConstantTime.
  Variable P: prog.

  Definition is_pub (v: var_i) := (var_info_to_attr v.(v_info)).(va_pub).

  Definition pub_vars vars : Sv.t :=
    foldl (fun s v => if (is_pub v) then (Sv.add v s) else s) Sv.empty vars.

  Definition same_pubs s s' := forall f, f \in P -> seq_on (pub_vars f.2.(f_params)) s s'.

  Definition constant_time_ex c :=
    forall s1 s2 s1' s2' H H', same_pubs s1 s2 ->
      @Leakage_Ex.leakage s1 c s1' H = @Leakage_Ex.leakage s2 c s2' H'.

  Definition constant_time_instr c :=
    forall s1 s2 s1' s2' t1 t2, same_pubs s1 s2 ->
      Leakage_Instr.mtsem s1 c t1 s1' -> Leakage_Instr.mtsem s2 c t2 s2' -> t1 = t2.
End ConstantTime.

Module ArrAlloc.
  Variable glob_arr : var.

  Definition glob_acc_l s := MRaset glob_arr (Mconst (I64.repr s)).
  Definition glob_acc_r s := Mget glob_arr (Mconst (I64.repr s)).

  Fixpoint arralloc_e (e:mexpr) (st: Z) : mcmd :=
    match e with
    | Madd e1 e2 => (arralloc_e e1 (st * 3 + 0)) ++ (arralloc_e e2 (st * 3 + 1))
                 ++ [:: MCassgn (glob_acc_l (st * 3 + 2)) (Madd (glob_acc_r (st * 3 + 0)) (glob_acc_r (st * 3 + 1)))]
    | Mand e1 e2 => (arralloc_e e1 (st * 3 + 0)) ++ (arralloc_e e2 (st * 3 + 1))
                 ++ [:: MCassgn (glob_acc_l (st * 3 + 2)) (Mand (glob_acc_r (st * 3 + 0)) (glob_acc_r (st * 3 + 1)))]
    | _ => [:: MCassgn (glob_acc_l st) e]
    end.

  Fixpoint arralloc_i (i:minstr) : mcmd :=
    match i with
    | MCassgn x e => (MCassgn x (glob_acc_r 0)) :: (arralloc_e e 0)
    end.

  Definition arralloc_cmd (c:mcmd) : mcmd :=
    foldr (fun i c' => arralloc_i i ++ c') [::] c.

  Lemma arralloc_cat (c1 c2: mcmd) :
    arralloc_cmd (c1 ++ c2) = (arralloc_cmd c1) ++ (arralloc_cmd c2).
  Proof.
    elim: c1=> // a l IH /=.
    by rewrite IH catA.
  Qed.

  Variable P: prog.

  (*
   * Try with Leakage_Ex
   *)
  Module Ex_Proof.
  Import Leakage_Ex.
  Lemma arralloc_i_ct i:
    constant_time_ex P [:: i]
    -> constant_time_ex P (arralloc_i i).
  Proof.
    case: i=> r e Hsrc /=.
    elim: e Hsrc=> /= [v|w|b|e1 IH1 e2 IH2| |] Hsrc; try (
    move=> s1 s2 s1' s2' H H' Hpub;
    rewrite /leakage /=;
    move: H=> /msem_inv [s1'' [Hi1 /msem_inv [s1''' [Hc1 Hskip1]]]];
    move: H'=> /msem_inv [s2'' [Hi2 /msem_inv [s2''' [Hc2 Hskip2]]]] //).
    move=> s1 s2 s1' s2' H H' Hpub.
    rewrite /leakage /=.
    move: H=> /msem_inv [s1'' [Hi1 Hc1]] /=.
    move: H'=> /msem_inv [s2'' [Hi2 Hc2]] /=.
    move: (leakage_cat Hc2)=> [s2''' [p' [p'' H2]]].
  Admitted.

  Lemma ct_head a l:
    constant_time_ex P (a :: l)
    -> constant_time_ex P [:: a].
  Proof.
    elim: l=> // a' l IH H.
    apply: IH.
    move=> s1 s2 s1' s2' H1 H2 Hpub.
    rewrite /constant_time_ex in H.
  Admitted.

  Theorem preserve_ct: forall c,
    constant_time_ex P c
    -> constant_time_ex P (arralloc_cmd c).
  Proof.
    elim=> // a l IH Hsrc.
    rewrite /=.
    move=> s1 s2 s1' s2' H H' Hpub.
    move: (leakage_cat H)=> [s1'' [p'1 [p''1 ->]]].
    move: (leakage_cat H')=> [s2'' [p'2 [p''2 ->]]].
    congr (trace_cat _ _).
    apply: arralloc_i_ct=> //.

    move=> s1'0 s2'0 s1'1 s2'1 H0 H'0 Hpub'.

    rewrite /leakage /=.
    move: H0=> /msem_inv [s1'2 [Hs1'2 Hskip1]].
    rewrite /=.
  Admitted.
  End Ex_Proof.

  Module Instr_Proof.
  Import Leakage_Instr.
  Lemma arralloc_i_ct i:
    constant_time_instr P [:: i]
    -> constant_time_instr P (arralloc_i i).
  Proof.
    case: i=> r e Hsrc /=.
    elim: e Hsrc=> /= [v|w|b|e1 IH1 e2 IH2| |] Hsrc; try (
    move=> s1 s2 s1' s2' t1 t2 Hpub;
    move=> /mtsem_inv /= [s1_1 [t1_1 [Hi1 [Hc1 Ht1]]]];
    move: Hc1=> /mtsem_inv /= [s1_2 [t1_2 [Hi1' [Hc1 Ht1']]]];
    rewrite -{}Ht1' in Hc1;
    move: Hc1=> /mtsem_inv [_ Ht1'2];
    rewrite {}Ht1'2 in Ht1;
    move=> /mtsem_inv /= [s2_1 [t2_1 [Hi2 [Hc2 Ht2]]]];
    move: Hc2=> /mtsem_inv /= [s2_2 [t2_2 [Hi2' [Hc2 Ht2']]]];
    rewrite -{}Ht2' in Hc2;
    move: Hc2=> /mtsem_inv [_ Ht2'2];
    rewrite {}Ht2'2 in Ht2;
    by rewrite Ht2 Ht1).
    move=> s1 s2 s1' s2' t1 t2 Hpub.
    admit. (* Annoying! *)
  Admitted.

  Lemma ct_head a l:
    (forall s, exists s' t, mtsem s (l ++ [:: a]) t s') ->
    constant_time_instr P (l ++ [:: a]) -> constant_time_instr P l.
  Proof.
    move=> Hsem H s1 s2 s1' s2' t1 t2 Hpub H1 H2.
    rewrite /constant_time_instr in H.
    move: (Hsem s1)=> [s1'' [t1' Hs1]].
    move: (Hsem s2)=> [s2'' [t2' Hs2]].
    move: H=> /(_ _ _ _ _ _ _ Hpub Hs1 Hs2) H.
    move: Hs1=> /mtsem_cat_inv [s1'_ [t1_ [t1'' [Hc1 [Hi1 Ht1]]]]].
    move: Hi1=> /mtsem_inv [s1''_ [t1'_ [Hi1 [Hskip1 Ht1'_]]]].
    move: Hs2=> /mtsem_cat_inv [s2'_ [t2_ [t2'' [Hc2 [Hi2 Ht2]]]]].
    move: Hi2=> /mtsem_inv [s2''_ [t2'_ [Hi2 [Hskip2 Ht2'_]]]].
    have: t1_ = t2_.
      rewrite {}Ht2'_ in Ht2.
      rewrite {}Ht1'_ in Ht1.
      rewrite {}Ht2 {}Ht1 in H.
  Admitted.

  Theorem preserve_ct: forall c,
    constant_time_instr P c
    -> constant_time_instr P (arralloc_cmd c).
  Proof.
    elim/List.rev_ind=> // a l IH Hsrc.
    rewrite arralloc_cat.
    move=> s1 s2 s1' s2' t1 t2 Hpub.
    move=> /mtsem_cat_inv [s1'' [t1_1 [t1_2 [Hc1 [/= Hi1 ->]]]]].
    rewrite cats0 in Hi1.
    move=> /mtsem_cat_inv [s2'' [t2_1 [t2_2 [Hc2 [/= Hi2 ->]]]]].
    rewrite cats0 in Hi2.
    congr (_ ++ _).
    have Hl: constant_time_instr P l.
      apply: (ct_head _ Hsrc).
      admit.
    exact: (IH Hl _ _ _ _ _ _ Hpub Hc1 Hc2).
    case: a Hsrc Hi1 Hi2=> r e Hsrc /= Hi1 Hi2.
    move: Hi1=> /mtsem_inv [s1_3 [t1_3 [Hi1 [Hc1' ->]]]].
    move: Hi2=> /mtsem_inv [s2_3 [t2_3 [Hi2 [Hc2' ->]]]].
    rewrite /=.
    congr (_ :: _).
    admit.
  Admitted.
  End Instr_Proof.
End ArrAlloc.
