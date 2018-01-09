Require Import x86_variables.
Import Utf8.
Import all_ssreflect.
Import compiler_util sem x86_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Lemma get_var_type vm x v :
  get_var vm x = ok v -> type_of_val v = vtype x.
Proof.
by apply: on_vuP => [t ? <-|_ [<-]//]; apply: type_of_to_val.
Qed.

(* -------------------------------------------------------------------- *)
Definition to_rbool (v : value) :=
  match v with
  | Vbool   b    => ok (Def b)
  | Vundef sbool => ok Undef
  | _            => type_error
  end.

Lemma to_rbool_inj v b b' :
  to_rbool v = ok b →
  to_rbool v = ok b' →
  b = b'.
Proof. by case: v => // [ v | [] // ] [<-] [<-]. Qed.

(* -------------------------------------------------------------------- *)
Definition of_rbool (v : RflagMap.rflagv) :=
  if v is Def b then Vbool b else Vundef sbool.

(* -------------------------------------------------------------------- *)
Lemma to_rboolK rfv : to_rbool (of_rbool rfv) = ok rfv.
Proof. by case: rfv. Qed.

(* -------------------------------------------------------------------- *)
Definition eqflags (m: estate) (rf: rflagmap) : Prop :=
  ∀ f v, get_var (evm m) (var_of_flag f) = ok v → value_uincl v (of_rbool (rf f)).

(* -------------------------------------------------------------------- *)
Definition value_of_bool (b: exec bool) : exec value :=
  match b with
  | Ok b => ok (Vbool b)
  | Error ErrAddrUndef => ok (Vundef sbool)
  | Error e => Error e
  end.

(* -------------------------------------------------------------------- *)
Lemma xgetflag_ex ii m rf x f v :
  eqflags m rf →
  rflag_of_var ii x = ok f →
  get_var (evm m) x = ok v →
  value_uincl v (of_rbool (rf f)).
Proof.
move: (@var_of_flag_of_var x).
move => h eqm; case: x h => -[] //= x.
rewrite /flag_of_var /=.
case: rflag_of_string => [vx|] // /(_ _ erefl) <- {x} [<-] ok_v.
by move/(_ _ _ ok_v): eqm.
Qed.

Corollary xgetflag_b ii m rf x f v b :
  eqflags m rf →
  rflag_of_var ii x = ok f →
  get_var (evm m) x = ok v →
  to_bool v = ok b →
  rf f = Def b.
Proof.
move => eqm ok_f ok_v ok_b.
have := xgetflag_ex eqm ok_f ok_v.
case: {ok_v} v ok_b => //.
- by move => b' [<-]; case: (rf _) => // ? ->.
by case.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ok_sem_op1_b f v b :
  sem_op1_b f v = ok b ->
    exists2 vb, to_bool v = ok vb & b = Vbool (f vb).
Proof.
rewrite /sem_op1_b /mk_sem_sop1; t_xrbindP => /= vb ->.
by move=> ok_b; exists vb.
Qed.

(* -------------------------------------------------------------------- *)
Lemma eval_assemble_cond ii gd m rf e c v:
  eqflags m rf →
  assemble_cond ii e = ok c →
  sem_pexpr gd m e = ok v →
  ∃ v', value_of_bool (eval_cond c rf) = ok v' ∧ value_uincl v v'.
Proof.
move=> eqv; case: e => //.
+ move => x /=; t_xrbindP => r ok_r ok_ct ok_v.
  have := xgetflag_ex eqv ok_r ok_v.
  by case: {ok_r ok_v} r ok_ct => // -[<-] {c} /= h; eexists; split; eauto; case: (rf _).
+ do 2! case=> //; move=> x /=; t_xrbindP => r.
  move => ok_r ok_ct vx ok_vx /ok_sem_op1_b [vb ok_vb -> {v}].
  have := xgetflag_b eqv ok_r ok_vx ok_vb.
  by case: {ok_r ok_vx ok_vb} r ok_ct => // -[<-] {c} /= -> /=; eexists.
Admitted.
