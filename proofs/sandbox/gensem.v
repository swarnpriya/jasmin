(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Notation onth s n := (nth None (map Some s) n).

Definition oseq {T : Type} (s : seq (option T)) :=
  if size s == size (pmap idfun s) then Some (pmap idfun s) else None.

Lemma pmap_idfun_some {T : Type} (s : seq T) :
  pmap idfun [seq Some x | x <- s] = s.
Proof. by elim: s => /= [|x s ->]. Qed.

Lemma oseqP {T : eqType} (s : seq (option T)) (u : seq T) :
  (oseq s == Some u) = (s == [seq Some x | x <- u]).
Proof.
apply/eqP/eqP=> [|->] //; last first.
+ by rewrite /oseq pmap_idfun_some size_map eqxx.
rewrite /oseq; case: ifP=> // /eqP eqsz [<-].
rewrite pmapS_filter map_id -{1}[s]filter_predT.
apply: eq_in_filter=> x x_in_s /=; move/esym/eqP: eqsz.
by rewrite size_pmap -all_count => /allP /(_ _ x_in_s).
Qed.

(* -------------------------------------------------------------------- *)
Fixpoint all2 {T U : Type} (p : T -> U -> bool) s1 s2 :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1, x2 :: s2 => p x1 x2 && all2 p s1 s2
  | _, _ => false
  end.

Lemma all2P {T U : Type} (p : T -> U -> bool) s1 s2:
    all2 p s1 s2
  = (size s1 == size s2) && (all [pred xy | p xy.1 xy.2] (zip s1 s2)).
Proof.
by elim: s1 s2 => [|x s1 ih] [|y s2] //=; rewrite ih andbCA eqSS.
Qed.

(* -------------------------------------------------------------------- *)
Parameter var : countType.
Parameter mem : Type.

Parameter vCF : var.

Inductive value :=
  | VInt  of int
  | VBool of bool.

Coercion VInt : int >-> value.
Coercion VBool : bool >-> value.

Parameter get : mem -> var -> value.
Parameter set : mem -> var -> value -> mem.

Definition sets (m : mem) (x : seq var) (v : seq value) :=
  if size x == size v then
    Some (foldl (fun m xv => set m xv.1 xv.2) m (zip x v))
  else None.

Inductive expr := EVar of var | EInt of int.

Axiom expr_eqMixin : Equality.mixin_of expr.
Canonical expr_eqType := EqType expr expr_eqMixin.

Definition eval (m : mem) (e : expr) :=
  match e return value with
  | EVar x => get m x
  | EInt i => i
  end.

Inductive cmd_name := ADDC | SUBC.

Definition cmd : Type := cmd_name * seq var * seq expr.

Parameter addc : int * int * bool -> int * bool.
Parameter subc : int * int * bool -> int * bool.

Definition sem_addc_val (args : seq value) :=
  if args is [:: VInt x; VInt y; VBool c] then
     let: (z, c) := addc (x, y, c) in Some [:: VInt z; VBool c]
  else None.

Definition sem_addc (m : mem) (outv : seq var) (inv : seq expr) :=
  if sem_addc_val [seq eval m x | x <- inv] is Some res then
    sets m outv res
  else None.

Definition sem_subc_val (args : seq value) :=
  if args is [:: VInt x; VInt y; VBool c] then
     let: (z, c) := subc (x, y, c) in Some [:: VInt z; VBool c]
  else None.

Definition sem_subc (m : mem) (outv : seq var) (inv : seq expr) :=
  if sem_subc_val [seq eval m x | x <- inv] is Some res then
    sets m outv res
  else None.

Definition semc (m : mem) (c : cmd) : option mem :=
  match c with
  | (ADDC, outv, inv) => sem_addc m outv inv
  | (SUBC, outv, inv) => sem_subc m outv inv
  end.

(* -------------------------------------------------------------------- *)
Inductive arg_desc :=
| ADImplicit of var
| ADExplicit of nat.

(* -------------------------------------------------------------------- *)
Module ADEq.
Definition code (ad : arg_desc) :=
  match ad with
  | ADImplicit x => GenTree.Node 0 [:: GenTree.Leaf (pickle x)]
  | ADExplicit x => GenTree.Node 1 [:: GenTree.Leaf x]
  end.

Definition decode (c : GenTree.tree nat) :=
  match c with
  | GenTree.Node 0 [:: GenTree.Leaf x] =>
      if unpickle x is Some x then Some (ADImplicit x) else None
  | GenTree.Node 1 [:: GenTree.Leaf x] =>
      Some (ADExplicit x)
  | _ => None
  end.

Lemma codeK : pcancel code decode.
Proof. by case=> //= x; rewrite pickleK. Qed.
End ADEq.

Definition arg_desc_EqMixin := PcanEqMixin ADEq.codeK.
Canonical arg_desc_EqType := EqType arg_desc arg_desc_EqMixin.

(* -------------------------------------------------------------------- *)
Inductive arg_ty := TYVar | TYLiteral | TYVL.

Definition locmd : Type := cmd_name * seq var.

Definition sem_ad_in (ad : arg_desc) (xs : seq expr) : option expr :=
  match ad with
  | ADImplicit x => Some (EVar x)
  | ADExplicit n => onth xs n
  end.

Definition sem_ad_out (ad : arg_desc) (xs : seq expr) : option var :=
  match ad with
  | ADImplicit x => Some x
  | ADExplicit n =>
      if onth xs n is Some (EVar y) then Some y else None
  end.

(* -------------------------------------------------------------------- *)
Inductive register := R1 | R2 | R3.
Inductive flag     := CF.
Inductive ireg     := IRReg of register | IRImm of int.

Inductive low_instr :=
| ADDC_lo of register & ireg
| SUBC_lo of register & ireg.

Record lomem := {
  lm_reg : register -> int;
  lm_fgs : flag -> bool;
}.

Parameter eval_reg : lomem -> register -> int.
Parameter eval_ireg : lomem -> ireg -> int.
Parameter eval_flag : lomem -> flag -> bool.
Parameter write_flag : lomem -> flag -> bool -> lomem.
Parameter write_reg : lomem -> register -> int -> lomem.

Definition interp_ty (ty : arg_ty) :=
  match ty with
  | TYVar     => register
  | TYLiteral => int
  | TYVL      => ireg
  end.

Fixpoint interp_tys (tys : seq arg_ty) :=
  if tys is ty :: tys then
    interp_ty ty -> interp_tys tys
  else low_instr.

Parameter register_of_var : var -> option register.

Definition foo1 {T} (ty : arg_ty) (arg : expr) :=
  match ty, arg return (interp_ty ty -> T) -> option T with
  | TYVar, EVar x => fun op =>
      if register_of_var x is Some r then Some (op r) else None
  | TYVL, EVar x => fun op =>
      if register_of_var x is Some r then Some (op (IRReg r)) else None
  | TYVL, EInt i => fun op => Some (op (IRImm i))
  | TYLiteral, EInt i => fun op => Some (op i)
  | _, _ => fun op => None
  end.

Fixpoint foon (tys : seq arg_ty) (args : seq expr)
  : interp_tys tys -> option low_instr :=

  match tys, args return interp_tys tys -> option low_instr with
  | ty :: tys, arg :: args => fun op =>
      if @foo1 _ ty arg op is Some op then
        @foon tys args op
      else None

  | [::], [::] =>
      fun op => Some op

  | _, _ =>
      fun op => None
  end.

(* -------------------------------------------------------------------- *)
Record instr_desc := {
  id_name : cmd_name;
  id_in   : seq arg_desc;
  id_out  : seq arg_desc;
  id_lo   : seq arg_ty;
  id_sem  : interp_tys id_lo;
}.

Definition sem_id
  (m : mem) (id : instr_desc) (xs : seq expr) : option mem
:=
  let: inx  := oseq [seq sem_ad_in  ad xs | ad <- id.(id_in )] in
  let: outx := oseq [seq sem_ad_out ad xs | ad <- id.(id_out)] in

  if (inx, outx) is (Some inx, Some outx) then
    match id.(id_name) with
    | ADDC => sem_addc m outx inx
    | SUBC => sem_subc m outx inx
    end
  else None.

(* -------------------------------------------------------------------- *)
Definition sem_lo (m : lomem) (i : low_instr) : lomem :=
  match i with
  | ADDC_lo r x =>
      let v1 := eval_reg  m r in
      let v2 := eval_ireg m x in
      let c  := eval_flag m CF in

      let: (res, cf) := addc (v1, v2, c) in

      write_reg (write_flag m CF c) r res

  | SUBC_lo r x =>
      let v1 := eval_reg  m r in
      let v2 := eval_ireg m x in
      let c  := eval_flag m CF in

      let: (res, cf) := subc (v1, v2, c) in

      write_reg (write_flag m CF c) r res
  end.

(* -------------------------------------------------------------------- *)
Definition ADDC_desc := {|
  id_name := ADDC;
  id_in   := [:: ADExplicit 0; ADExplicit 1; ADImplicit vCF];
  id_out  := [:: ADExplicit 0; ADImplicit vCF];
  id_lo   := [:: TYVar; TYVL];
  id_sem  := ADDC_lo;
|}.

(* -------------------------------------------------------------------- *)
Definition SUBC_desc := {|
  id_name := SUBC;
  id_in   := [:: ADExplicit 0; ADExplicit 1; ADImplicit vCF];
  id_out  := [:: ADExplicit 0; ADImplicit vCF];
  id_lo   := [:: TYVar; TYVL];
  id_sem  := SUBC_lo;
|}.

(* -------------------------------------------------------------------- *)
Definition get_id (c : cmd_name) :=
  match c with
  | ADDC => ADDC_desc
  | SUBC => SUBC_desc
  end.

(* -------------------------------------------------------------------- *)
Lemma get_id_ok c : (get_id c).(id_name) = c.
Proof. by case: c. Qed.

(* -------------------------------------------------------------------- *)
Definition compile_lo (c : cmd_name) (args : seq expr) :=
  @foon (get_id c).(id_lo) args (get_id c).(id_sem).

(* -------------------------------------------------------------------- *)
Definition check_cmd_arg (loargs : seq expr) (x : expr) (ad : arg_desc) :=
  match ad with
  | ADImplicit y => x == EVar y
  | ADExplicit n => (n < size loargs) && (x == nth x loargs n)
  end.

(* -------------------------------------------------------------------- *)
Definition check_cmd_res (loargs : seq expr) (x : var) (ad : arg_desc) :=
  match ad with
  | ADImplicit y => x == y
  | ADExplicit n => (n < size loargs) && (EVar x == nth (EVar x) loargs n)
  end.

(* -------------------------------------------------------------------- *)
Definition check_cmd_args
  (c : cmd_name) (outx : seq var) (inx : seq expr) (loargs : seq expr)
:=
  let: id := get_id c in

     all2 (check_cmd_res loargs) outx id.(id_out)
  && all2 (check_cmd_arg loargs) inx  id.(id_in ).

(* -------------------------------------------------------------------- *)
Lemma Pin (loargs hiargs : seq expr) (ads : seq arg_desc) :
     all2 (check_cmd_arg loargs) hiargs ads
  -> oseq [seq sem_ad_in ad loargs | ad <- ads] = Some hiargs.
Proof.
rewrite all2P => /andP [/eqP eqsz h]; apply/eqP; rewrite oseqP.
apply/eqP/(eq_from_nth (x0 := None)); rewrite ?(size_map, eqsz) //.
move=> i lt_i_ads; have ad0 : arg_desc := (ADExplicit 0).
rewrite (nth_map ad0) // (nth_map (EVar vCF)) ?eqsz // /sem_ad_in.
set x1 := nth (EVar vCF) _ _; set x2 := nth ad0 _ _.
have -/(allP h) /=: (x1, x2) \in zip hiargs ads.
+ by rewrite -nth_zip // mem_nth // size_zip eqsz minnn.
rewrite /check_cmd_arg; case: x2 => [? /eqP->//|].
by move=> n /andP[len /eqP->]; rewrite (nth_map x1).
Qed.

(* -------------------------------------------------------------------- *)
Lemma Pout (loargs : seq expr) (hiargs : seq var) (ads : seq arg_desc) :
     all2 (check_cmd_res loargs) hiargs ads
  -> oseq [seq sem_ad_out ad loargs | ad <- ads] = Some hiargs.
Proof.
rewrite all2P => /andP [/eqP eqsz h]; apply/eqP; rewrite oseqP.
apply/eqP/(eq_from_nth (x0 := None)); rewrite ?(size_map, eqsz) //.
move=> i lt_i_ads; have ad0 : arg_desc := (ADExplicit 0).
rewrite (nth_map ad0) // (nth_map vCF) ?eqsz // /sem_ad_out.
set x1 := nth vCF _ _; set x2 := nth ad0 _ _.
have -/(allP h) /=: (x1, x2) \in zip hiargs ads.
+ by rewrite -nth_zip // mem_nth // size_zip eqsz minnn.
rewrite /check_cmd_res; case: x2 => [? /eqP->//|].
by move=> n /andP[len /eqP]; rewrite (nth_map (EVar x1)) // => <-.
Qed.

(* -------------------------------------------------------------------- *)
Theorem L c outx inx loargs m1 m2 :
     check_cmd_args c outx inx loargs
  -> semc m1 (c, outx, inx) = Some m2
  -> sem_id m1 (get_id c) loargs = Some m2.
Proof.
by case/andP=> h1 h2; rewrite /sem_id /semc (Pin h2) (Pout h1) get_id_ok.
Qed.
