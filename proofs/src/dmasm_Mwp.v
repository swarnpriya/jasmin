Require dmasm_Msem.

Import Utf8.
Import ssreflect.
Import ssrbool.
Import eqtype.
Import seq.
Import ZArith.

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
