Require dmasm_Msem.

Import Utf8.
Import Morphisms.
Import ssreflect.
Import ssrbool.
Import eqtype.
Import seq.
Import ZArith.
Local Open Scope Z_scope.

Import dmasm_utils.
Import dmasm_type.
Import dmasm_var.
Import dmasm_Ssem.
Import dmasm_Msem.

Definition hpred : Type :=
  svmap → Prop.

Notation "A ⊂ B" := (∀ x, A x → B x) (at level 80) : msem_scope.

Local Open Scope msem_scope.

Definition hoare (Pre: hpred) (c: mcmd) (Post: hpred) : Prop :=
  ∀ s s' : svmap,
    msem s c s' →
    Pre s → Post s'.

Lemma hoare_conseq (P1 Q1: hpred) (c: mcmd) (P2 Q2: hpred) :
  P2 ⊂ P1 → Q1 ⊂ Q2 →
  hoare P1 c Q1 → hoare P2 c Q2.
Proof. firstorder. Qed.

Lemma hoare_skip_core P : hoare P [::] P.
Proof. by move => s s' H; case (msem_inv H). Qed.

Lemma hoare_skip (Q P: hpred) : Q ⊂ P → hoare Q [::] P.
Proof. eauto using hoare_conseq, hoare_skip_core. Qed.

Lemma hoare_cons R P Q i c :
  hoare P [:: i] R →  hoare R c Q →  hoare P (i :: c) Q.
Proof.
  by
  move=> Hi Hc s s' /msem_inv [ s1 [Hi' Hc']] H;
  eauto using MEseq, MEskip.
Qed.

Lemma hoare_assgn (P: hpred) x e :
  hoare
    (λ s, ∀ v s',
        msem_mexpr s e = ok v →
        sset_var s x v = ok s' →
        P s')
    [:: MCassgn x e] P.
Proof.
  move=> s s1 / msem_inv [ s' [Hi /msem_inv]] ->.
  case: (msem_I_inv Hi) => v [ Hv Hs' ].
  firstorder.
Qed.

(* WP *)
(* A formula is a predicate over an environment that maps logical variables to value. *)
(* This predicate should be extensional *)

Definition env : Type := Mv.t ssem_t.
Definition env_ext (m m': env) : Prop :=
  ∀ x, (m.[x] = m'.[x])%mv.

Definition env_ext_refl m : env_ext m m := λ x, Logic.eq_refl.
Definition env_ext_sym m m' (H: env_ext m m') : env_ext m' m :=
  λ x, Logic.eq_sym (H x).
Definition env_ext_trans m' m m'' (H: env_ext m m') (H': env_ext m' m'') :
  env_ext m m'' :=
  λ x, Logic.eq_trans (H x) (H' x).

Lemma env_ext_empty m m' :
  (∀ x, m x = m' x) →
  env_ext (Mv.empty m) (Mv.empty m').
Proof. by move=> E x; rewrite ! Mv.get0. Qed.

Lemma env_ext_set m m' x v :
  env_ext m m' →
  (env_ext (m.[x <- v]) (m'.[x <- v]))%mv.
Proof.
  move=> E y.
  case: (x =P y) => [ <- | H ].
  rewrite ! Mv.setP_eq //.
  rewrite ! Mv.setP_neq //;
  case: eqP => //.
Qed.

Definition formula : Type :=
  sigT (Proper (env_ext ==> iff)).

Lemma formula_m (f: env → Prop) :
  (∀ s s', env_ext s s' → f s → f s') →
  Proper (env_ext ==> iff) f.
Proof.
  move=> E s s' H.
  split; eauto using env_ext_sym.
Qed.

Instance constant_formula_m (P: Prop) : Proper (env_ext ==> iff) (λ _, P) :=
  formula_m _ (λ _ _ _ (p: P), p).

Example ftrue: formula := existT _ (λ _, True) _.
Example ffalse: formula := existT _ (λ _, False) _.

Definition formula_of_hpred (P: hpred) : formula.
Proof.
  refine (existT _ (λ s: env, P (Fv.empty (λ x, s.[x])%mv)) _).
  apply formula_m.
  move=> s s' E H.
  refine (eq_ind _ P H _ _).
  apply Fv.map_ext. auto.
Defined.

Notation "⟨ P ⟩" := (formula_of_hpred P) : msem_scope.

Definition formula_denote (f: formula) : hpred :=
  λ s, projT1 f (Mv.empty (λ x, s.[x])%vmap).

Notation "⟦ f ⟧" := (formula_denote f) : msem_scope.

Lemma formula_of_hpred_denote P :
  ∀ s, ⟦ ⟨P⟩ ⟧ s ↔ P s.
Proof.
  unfold formula_of_hpred, formula_denote. simpl.
  by
  move=> s; split; move=> H; refine (eq_ind _ P H _ _); apply Fv.map_ext; move=> x;
  rewrite Fv.get0 Mv.get0.
Qed.

Inductive texpr : stype → Type :=
| Tvar v : texpr (vtype v)
| Tconst `(Z) : texpr sint
| Tbool `(bool) : texpr sbool
| Tadd (_ _: texpr sint) : texpr sint
| Tand (_ _: texpr sbool) : texpr sbool
.

Section SEM_TEXPR.
  Context (m: Mv.t ssem_t).
  Fixpoint sem_texpr ty (e: texpr ty) : ssem_t ty :=
    match e with
    | Tvar x => m.[x]
    | Tconst z => z
    | Tbool b => b
    | Tadd p q => sem_texpr sint p + sem_texpr sint q
    | Tand p q => sem_texpr sbool p && sem_texpr sbool q
    end%mv.
End SEM_TEXPR.

Lemma sem_texpr_m (s s': env) :
  env_ext s s' →
  ∀ ty e, sem_texpr s ty e = sem_texpr s' ty e.
Proof.
  move=> E ty e.
  elim: e => //; simpl; congruence.
Qed.

Definition stype_eq_dec (ty ty': stype) : { ty = ty' } + { True } :=
  match ty, ty' with
  | sint, sint => left Logic.eq_refl
  | sbool, sbool => left Logic.eq_refl
  | _, _ => right I
  end.

Fixpoint type_check_mexpr (e: mexpr) (ty: stype) : option (texpr ty) :=
  match e with
  | Mvar x =>
    match stype_eq_dec (vtype x) ty with
    | left EQ => Some (eq_rect _ _ (Tvar x) _ EQ)
    | right _ => None
    end
  | Mconst z => match ty with sint => Some (Tconst z) | _ => None end
  | Mbool b => match ty with sbool => Some (Tbool b) | _ => None end
  | Madd p q =>
    match type_check_mexpr p sint with
    | Some tp =>
    match type_check_mexpr q sint with
    | Some tq => match ty with sint => Some (Tadd tp tq) | _ => None end
    | None => None end
    | None => None end
  | Mand p q =>
    match type_check_mexpr p sbool with
    | Some tp =>
    match type_check_mexpr q sbool with
    | Some tq => match ty with sbool => Some (Tand tp tq) | _ => None end
    | None => None end
    | None => None end
  end.

Definition Some_inj {A} (a a': A) (H: Some a = Some a') : a = a' :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Definition ok_inj {E A} (a a': A) (H: Ok E a = ok a') : a = a' :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Lemma of_sval_to_sval ty x :
  of_sval ty (to_sval x) = ok x.
Proof. by move: x; case ty. Qed.

Lemma sto_int_inv x i :
  sto_int x = ok i →
  x = i.
Proof. case: x => // i' H; apply ok_inj in H. congruence. Qed.

Lemma sto_bool_inv x b :
  sto_bool x = ok b →
  x = b.
Proof. case: x => // i' H; apply ok_inj in H. congruence. Qed.

Lemma type_check_mexprP {e ty te} :
  type_check_mexpr e ty = Some te →
  ∀ s v,
  msem_mexpr s e = ok v →
  ∀ s',
  (∀ x, s.[x]%vmap = s'.[x]%mv) →
  of_sval _ v = ok (sem_texpr s' ty te).
Proof.
  elim: e ty te.
  - move=> v ty te. simpl. case: stype_eq_dec => //.
    move=> EQ H; apply Some_inj in H; subst.
    move=> s v' H; apply ok_inj in H; subst v'.
    move=> s' E. simpl. unfold sget_var. rewrite E.
    apply of_sval_to_sval.
  - move=> z [] // te H; apply Some_inj in H; subst.
    move=> s v H; apply ok_inj in H; subst v.
    reflexivity.
  - move=> b [] // te H; apply Some_inj in H; subst.
    move=> s v H; apply ok_inj in H; subst v.
    reflexivity.
  - move=> p IHp q IHq ty te.
    simpl.
    move: (IHp sint). clear IHp.
    case: (type_check_mexpr p _) => // tp IHp.
    specialize (IHp _ Logic.eq_refl).
    move: (IHq sint). clear IHq.
    case: (type_check_mexpr q _) => // tq IHq.
    specialize (IHq _ Logic.eq_refl).
    move: te. case: ty => // te H; apply Some_inj in H; subst.
    move=> s v.
    move=> H; case: (bindW H) => vp Ep. clear H.
    move=> H; case: (bindW H) => vq Eq. clear H.
    move=> H; case: (bindW H) => ip Tp. clear H.
    move=> H; case: (bindW H) => iq Tq. clear H.
    move=> H; apply ok_inj in H; subst.
    move=> s' E. simpl.
    specialize (IHp _ _ Ep _ E).
    specialize (IHq _ _ Eq _ E).
    apply sto_int_inv in IHp.
    apply sto_int_inv in IHq.
    apply sto_int_inv in Tp.
    apply sto_int_inv in Tq. congruence.
  - move=> p IHp q IHq ty te.
    simpl.
    move: (IHp sbool). clear IHp.
    case: (type_check_mexpr p _) => // tp IHp.
    specialize (IHp _ Logic.eq_refl).
    move: (IHq sbool). clear IHq.
    case: (type_check_mexpr q _) => // tq IHq.
    specialize (IHq _ Logic.eq_refl).
    move: te. case: ty => // te H; apply Some_inj in H; subst.
    move=> s v.
    move=> H; case: (bindW H) => vp Ep. clear H.
    move=> H; case: (bindW H) => vq Eq. clear H.
    move=> H; case: (bindW H) => bp Tp. clear H.
    move=> H; case: (bindW H) => bq Tq. clear H.
    move=> H; apply ok_inj in H; subst.
    move=> s' E. simpl.
    specialize (IHp _ _ Ep _ E).
    specialize (IHq _ _ Eq _ E).
    apply sto_bool_inv in IHp.
    apply sto_bool_inv in IHq.
    apply sto_bool_inv in Tp.
    apply sto_bool_inv in Tq. congruence.
Qed.

Definition wp_assgn (x: var) (e: mexpr) (f: formula) : formula.
  refine
  match type_check_mexpr e (vtype x) with
  | Some te =>
    existT _ (
    λ s,
    ∀ v, sem_texpr s (vtype x) te = v → projT1 f (s.[x <- v])%mv) _
  | None => ffalse
  end.
Proof.
  abstract (
  apply formula_m;
  move=> s s' E X v V;
  rewrite (projT2 f); [| apply env_ext_set, env_ext_sym, E ];
  apply X; etransitivity; [ apply sem_texpr_m, E | exact V ]).
Defined.

Lemma wp_assgn_sound x e f :
  hoare ⟦wp_assgn x e f⟧ [:: MCassgn x e] ⟦f⟧.
Proof.
  move=> s s1 /msem_inv [s' [H' /msem_inv]] ->.
  case: (msem_I_inv H') => v [Hv H]. clear H'.
  case: (bindW H) => [u Hu Hs']. clear H.
  apply ok_inj in Hs'. subst s'.
  unfold wp_assgn.
  case (type_check_mexpr _ _) eqn: EQ. 2: firstorder.
  move: (type_check_mexprP EQ _ _ Hv) => R.
  unfold formula_denote. simpl.
  move=> X.
  rewrite (projT2 f). apply X. clear X.
  Focus 2.
  move=> y. rewrite Mv.get0.
  case: (x =P y).
  move=> <-. rewrite ! (Fv.setP_eq, Mv.setP_eq). reflexivity.
  move=> NE. rewrite ! (Fv.setP_neq, Mv.setP_neq) //; case: eqP => //.
  apply: ok_inj. etransitivity. 2: apply Hu.
  symmetry. apply R.
  auto.
Qed.

Definition wp_minstr (i: minstr) (f: formula) : formula :=
  match i with
  | MCassgn x e => wp_assgn x e f
  end.

Lemma wp_minstr_sound i f :
  hoare ⟦wp_minstr i f⟧ [:: i] ⟦f⟧.
Proof.
  case i => x e.
  apply: wp_assgn_sound.
Qed.

Definition wp (c: mcmd) (f: formula) : formula :=
  foldr wp_minstr f c.

Lemma wp_sound c f :
  hoare ⟦wp c f⟧ c ⟦f⟧.
Proof.
  elim: c f.
  - auto using hoare_skip_core.
  - simpl; eauto using wp_minstr_sound, hoare_cons.
Qed.

Print Assumptions wp_sound.

Lemma hoare_by_wp (P: hpred) c Q :
  P ⊂ ⟦wp c ⟨Q⟩⟧ →
  hoare P c Q.
Proof.
  move=> E.
  eapply hoare_conseq. exact E. 2: apply wp_sound.
  apply formula_of_hpred_denote.
Qed.

Section Example.
  Let x : var := Var sint "x".
  Let y : var := Var sint "y".

  Let p : mcmd :=
    MCassgn x (Mconst 1)
 :: MCassgn x (Madd (Mvar x) (Mconst 1))
 :: MCassgn y (Madd (Mvar x) (Mvar x))
 :: MCassgn x (Madd (Mvar y) (Mvar y))
 :: MCassgn y (Madd (Mvar x) (Mvar x))
 :: MCassgn x (Madd (Mvar y) (Mvar y))
 :: MCassgn y (Madd (Mvar x) (Mvar x))
 :: MCassgn x (Madd (Mvar y) (Mvar y))
 :: nil.

  Goal hoare (λ _, True) p (λ e, Z.even e.[x]%vmap).
  Proof.
    apply hoare_by_wp. move=> q _.
    simpl. setoid_rewrite Mv.setP_eq.
    intuition subst.
    reflexivity.
  Abort.

End Example.

(*

(* WP *)
(* A “formula” is a list of variables and a predicate over the values of these variables *)

Fixpoint vpred (vars: seq var) : Type :=
  match vars with
  | [::] => Prop
  | x :: vars' => ssem_t (vtype x) → vpred vars'
  end.

Definition formula : Type := { vars : seq var & vpred vars }.

Example vtrue : formula := existT _ [::] True.
Example vfalse : formula := existT _ [::] False.

Section FormulaDenote.
  Context (s: svmap).
  Fixpoint formula_denote_aux (vars: seq var) : vpred vars → Prop :=
    match vars with
    | [::] => λ P, P
    | x :: vars' => λ P, formula_denote_aux vars' (P (s.[x])%vmap)
    end.
End FormulaDenote.

Definition formula_denote (f: formula) : hpred :=
  λ s,
  let 'existT vars P := f in
  formula_denote_aux s vars P.

Notation "⟦ f ⟧" := (formula_denote f) : msem_scope.

Section ABSTRACT_VAR.
  Context (x: var).
  Fixpoint abstract_var_aux (vars: seq var) :
    { vars': seq var & vpred vars → ssem_t (vtype x) → vpred vars' } :=
      match vars
      return { vars' : seq var & vpred vars → ssem_t (vtype x) → vpred vars' }
      with
      | [::] => existT _ [::] (λ P _, P)
      | y :: vars' =>
        let 'existT q f := abstract_var_aux vars' in
        match x =P y with
        | ReflectT EQ => existT _ q (λ h v, f (h (eq_rect _ (λ a, ssem_t (vtype a)) v _ EQ)) v)
        | ReflectF NE => existT (λ q, vpred (y :: vars') → ssem_t (vtype x) → vpred q) (y :: q) (λ h vx vy, f (h vy) vx)
        end
      end.
End ABSTRACT_VAR.

Definition abstract_var (x: var) (f: formula) :
  { vars': seq var & ssem_t (vtype x) → vpred vars' } :=
  let 'existT vars g := f in
  let 'existT vars' h := abstract_var_aux x vars in
  existT _ vars' (h g).

Section Example0.
  Local Open Scope Z_scope.
  Let x : var := Var sbool "x".
  Let y : var := Var sint "y".

  Let P (b: bool) (n: Z) : Prop :=
    if b then Z.gcd n 4 = 2 else 0 < n.

  Let f : formula := existT _ [:: x ; y ] P.

  Let s : svmap := (svmap0.[ x <- true].[ y <- 42 ])%vmap.

  Goal ⟦f⟧ s.
  Proof.
    unfold s, P. simpl.
    rewrite !(Fv.setP_eq, Fv.setP_neq) //.
  Abort.
End Example0.

(* λ v1 … vn w1 … wn,
∀ x, x = ⟦e⟧ v1 … vn → ⟦f⟧^x x w1 … wn
 *)
Definition wp_assgn (x: var) (e: mexpr) (f: formula) : formula :=
  if true then
    let 'existT vars P := f in
    f
  else vtrue.

Lemma wp_assgn_sound x e f :
  hoare ⟦wp_assgn x e f⟧ [:: MCassgn x e] ⟦f⟧.
Proof.
Admitted.

Definition wp_minstr (i: minstr) (f: formula) : formula :=
  match i with
  | MCassgn x e => wp_assgn x e f
  end.

Lemma wp_minstr_sound i f :
  hoare ⟦wp_minstr i f⟧ [:: i] ⟦f⟧.
Proof.
  case i => x e.
  apply: wp_assgn_sound.
Qed.

Definition wp (c: mcmd) (f: formula) : formula :=
  foldr wp_minstr f c.

Lemma wp_sound c f :
  hoare ⟦wp c f⟧ c ⟦f⟧.
Proof.
  elim: c f.
  - auto using hoare_skip_core.
  - simpl; eauto using wp_minstr_sound, hoare_cons.
Qed.

*)
