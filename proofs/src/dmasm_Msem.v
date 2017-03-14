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
Fixpoint trace_expr (s: svmap) (e: mexpr) :=
  match e with
  | Mvar v => [::]
  | Mbool b => [::]
  | Mconst z => [::]
  | Madd e1 e2 => (trace_expr s e1) ++ (trace_expr s e2)
  | Mand e1 e2 => (trace_expr s e1) ++ (trace_expr s e2)
  | Mget x e => [:: msem_mexpr s e]
  end.

Definition trace_instr (s: svmap) (c: minstr) :=
  match c with
  | MCassgn _ e => trace_expr s e
  end.
End Trace.

(*
 * Definition 1/4: use a fixpoint
 *)
Module Leakage_Fix.
Fixpoint leakage_fix (s: svmap) (c: mcmd) (s': svmap) (p: msem s c s') {struct p} : seq (exec svalue).
  refine
  (match c as c0 return c = c0 -> seq (exec svalue) with
  | [::] => fun _ => [::]
  | i :: c' => fun (Hc: c = i::c') =>
    (Trace.trace_instr s i) ++
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
  exact (ExT ((Trace.trace_instr s i) ++ q)).
Defined.

Lemma leakage_irr (s: svmap) (c: mcmd) (s': svmap) (p: msem s c s') (p': msem s c s'):
  leakage p = leakage p'.
Proof.
  case: c p p'=> [p p'|a l IH].
Admitted.

Lemma leakage_cat s c1 c2 s' (p: msem s (c1 ++ c2) s'):
  exists s1 p' p'',
  @leakage s (c1 ++ c2) s' p = trace_cat (@leakage s c1 s1 p') (@leakage s1 c2 s' p'').
Proof.
  move: (msem_cat_inv p)=> [s1 [p' p'']].
  exists s1; exists p'; exists p''.
  elim: c1 s p p'=> /= [s p p'|a l IH s p p'].
  move: p'=> /msem_inv H.
  admit.
  move: p=> /msem_inv [s2 [Hs2 Hs2']].
  move: p'=> /msem_inv [s3 [Hs3 Hs3']].
  move: (IH _ Hs2').
Admitted.
End Leakage_Ex.

(*
 * Definition 3/4: instrumented big step semantics
 *)
Module Leakage_Instr.
  (* TODO *)
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

  Variable leakage: forall s c s', msem s c s' -> Leakage_Ex.trace.

  Definition is_pub (v: var_i) := (var_info_to_attr v.(v_info)).(va_pub).

  Definition pub_vars vars : Sv.t :=
    foldl (fun s v => if (is_pub v) then (Sv.add v s) else s) Sv.empty vars.

  Definition same_pubs s s' := forall f, f \in P -> seq_on (pub_vars f.2.(f_params)) s s'.

  Definition constant_time c :=
    forall s1 s2 s1' s2' H H',
      same_pubs s1 s2 -> @leakage s1 c s1' H = @leakage s2 c s2' H'.
End ConstantTime.

Section ArrAlloc.
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
    List.fold_right (fun i c' => arralloc_i i ++ c') [::] c.

  Variable P: prog.

  Theorem preserve_ct: forall c,
    constant_time P Leakage_Ex.leakage c
    -> constant_time P Leakage_Ex.leakage (arralloc_cmd c).
  Proof.
    elim=> // a l IH Hsrc.
    rewrite /=.
    move=> s1 s2 s1' s2' H H' Hpub.
  Admitted.
End ArrAlloc.
