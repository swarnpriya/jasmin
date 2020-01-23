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

(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect.
Require Import ZArith psem compiler_util.
Require Export unrolling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.
Local Open Scope seq_scope.

Section PROOF.

  Variable p : prog.
  Notation gd := (p_globs p).

  Let p' := unroll_prog p.

  Let Pi_r (s:estate) (i:instr_r) (s':estate) :=
    forall ii, sem p' s (unroll_i (MkI ii i)) s'.

  Let Pi (s:estate) (i:instr) (s':estate) :=
    sem p' s (unroll_i i) s'.

  Let Pc (s:estate) (c:cmd) (s':estate) :=
    sem p' s (unroll_cmd unroll_i c) s'.

  Let Pfor (i:var_i) vs s c s' :=
    sem_for p' i vs s (unroll_cmd unroll_i c) s'
    /\ forall ii, sem p' s
      (flatten (map (fun n => assgn ii i (Pconst n) :: (unroll_cmd unroll_i c)) vs)) s'.

  Let Pfun m1 fn vargs m2 vres :=
    sem_call p' m1 fn vargs m2 vres.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. exact: Eskip. Qed.

  Local Lemma Hcons : sem_Ind_cons p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c Hsi Hi Hsc Hc.
    exact: (sem_app Hi Hc).
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p Pi_r Pi.
  Proof. move=> ii i s1 s2 _ Hi; exact: Hi. Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' hv hv' hw ii.
    by apply: sem_seq1; apply: EmkI; apply: Eassgn; eauto.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es Hw ii.
    by apply: sem_seq1; apply: EmkI; apply: Eopn.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hb Hsc Hc ii.
    by apply: sem_seq1; apply: EmkI; apply: Eif_true.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hb Hsc Hc ii.
    by apply: sem_seq1; apply: EmkI; apply: Eif_false.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' Hsc Hc Hb Hsc' Hc' Hsi Hi ii.
    apply: sem_seq1; apply: EmkI; apply: Ewhile_true=> //; eauto=> /=.
    by move: Hi=> /(_ ii) /semE [?] [/sem_IE Hi /semE ->].
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p Pc Pi_r.
  Proof.
   move=> s1 s2 a c e c' Hsc Hc Hb ii.
   by apply: sem_seq1; apply: EmkI; apply: Ewhile_false.
  Qed.

  Local Lemma Hfor : sem_Ind_for p Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi Hlo Hhi Hc [Hfor Hfor'] ii /=.
    case Hlo': (is_const lo)=> [nlo|].
    + case Hhi': (is_const hi)=> [nhi|].
      + have ->: nlo = vlo.
          rewrite /is_const /= in Hlo'.
          by case: lo Hlo Hlo'=> //= z [] -> [] ->.
        have ->: nhi = vhi.
          rewrite /is_const /= in Hhi'.
          by case: hi Hhi Hhi'=> //= z [] -> [] ->.
        exact: Hfor'.
      apply: sem_seq1; apply: EmkI; apply: Efor; [apply: Hlo|apply: Hhi|apply: Hfor].
    apply: sem_seq1; apply: EmkI; apply: Efor; [apply: Hlo|apply: Hhi|apply: Hfor].
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move => s i c.
    split=> //=.
    exact: EForDone.
    move=> ii.
    apply: Eskip.
  Qed.

  Lemma write_var_Z i (z: Z) s s' :
    write_var i z s = ok s' ->
    vtype i = sint.
  Proof. by case: i => - [[] x]. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hw Hsc Hc Hsfor [Hfor Hfor']; split=> [|ii].
    apply: EForOne; [exact: Hw|exact: Hc|exact: Hfor].
    move: Hfor'=> /(_ ii) Hfor'.
    apply: Eseq.
    + apply: EmkI; apply: Eassgn. reflexivity. by rewrite (write_var_Z Hw). exact Hw.
    apply: sem_app.
    exact: Hc.
    exact: Hfor'.
  Qed.

  Local Lemma Hcall : sem_Ind_call p Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs Hexpr Hcall Hfun Hw ii'.
    apply: sem_seq1; apply: EmkI; apply: Ecall; [exact: Hexpr|exact: Hfun|exact: Hw].
  Qed.

  Local Lemma Hproc : sem_Ind_proc p Pc Pfun.
  Proof.
    move => m1 m2 fn f vargs vargs' s1 vm2 vres vres'.
    case: f=> fi ftyi fparams fc ftyo fres /= Hget Htyi Hw _ Hc Hres Htyo.
    apply: EcallRun.
    + by rewrite get_map_prog Hget.
    + exact: Htyi.
    + exact: Hw.
    + exact: Hc.
    + exact: Hres.
    exact: Htyo.
  Qed.

  Lemma unroll_callP f mem mem' va vr:
    sem_call p  mem f va mem' vr ->
    sem_call p' mem f va mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.
