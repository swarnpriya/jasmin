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
Definition rflags_of_lvm (vm : vmap) (rf : rflagmap) :=
  forall x r, rflag_of_string x = Some r ->
    match get_var vm {| vtype := sbool; vname := x |} with
    | Ok v =>
      match to_rbool v with
      | Ok b => rf r = b
      | _    => False
      end
    | _ => False
    end.

Definition eqflags (m: estate) (rf: rflagmap) : Prop :=
  rflags_of_lvm (evm m) rf.

(* -------------------------------------------------------------------- *)
Lemma xgetflag_ex ii m rf x f v :
  eqflags m rf →
  rflag_of_var ii x = ok f →
  get_var (evm m) x = ok v →
  exists2 b, to_rbool v = ok b & rf f = b.
Proof.
move => eqm; case: x => -[] //= x.
case E: rflag_of_string => [vx|] // [<-] ok_v.
have /= := get_var_type ok_v; case: v ok_v => //=.
+ move=> b ok_v _; exists (Def b) => //.
  by move/(_ _ _ E): eqm; rewrite ok_v /=.
case=> //= ok_v _; exists Undef => //.
by move/(_ _ _ E): eqm; rewrite ok_v /=.
Qed.

Corollary xgetflag_r ii m rf x f v b :
  eqflags m rf →
  rflag_of_var ii x = ok f →
  get_var (evm m) x = ok v →
  to_rbool v = ok b →
  rf f = b.
Proof.
move => eqm ok_f ok_v ok_b.
have [b' ok_b' ->] := xgetflag_ex eqm ok_f ok_v.
exact: (to_rbool_inj ok_b' ok_b).
Qed.

Corollary xgetflag_b ii m rf x f v b :
  eqflags m rf →
  rflag_of_var ii x = ok f →
  get_var (evm m) x = ok v →
  to_bool v = ok b →
  rf f = Def b.
Proof.
move => eqm ok_f ok_v ok_b.
apply: (xgetflag_r eqm ok_f ok_v).
by case: {ok_v} v ok_b => // [ b' | [] // ] [<-].
Qed.

(* -------------------------------------------------------------------- *)
Lemma ok_sem_op1_b f v b :
  sem_op1_b f v = ok b ->
    exists2 vb, to_bool v = ok vb & b = Vbool (f vb).
Proof.
rewrite /sem_op1_b /mk_sem_sop1; t_xrbindP => /= vb ->.
by move=> ok_b; exists vb.
Qed.

(*
Definition is_def (v: value) : bool :=
  if v is Vundef _ then false else true.

Definition as_bool (v: value) : bool :=
  if to_bool v is Ok b then b else true.

(* -------------------------------------------------------------------- *)
Lemma eval_assemble_cond ii gd m rf e c v:
  eqflags m rf →
  assemble_cond ii e = ok c →
  sem_pexpr gd m e = ok v →
  is_def v →
  ∃ b : bool,
    v = b ∧
    eval_cond c rf = ok b.
Proof.
move=> eqv; case: e => //.
+ move => x /=; t_xrbindP => r ok_r ok_ct ok_v.
  have [b ok_b] := xgetflag_ex eqv ok_r ok_v.
  by case: {ok_r ok_v} r ok_ct => // -[<-] {c} /= -> //;
    case: v ok_b => // b' [<-]; eauto.
+ do 2! case=> //; move=> x /=; t_xrbindP => r.
  move => ok_r ok_ct vx ok_vx /ok_sem_op1_b [vb ok_vb -> {v}].
  have := xgetflag_b eqv ok_r ok_vx ok_vb.
  by case: {ok_r ok_vx} r ok_ct => // -[<-] {c} /= ->; eauto.
Admitted.
*)
