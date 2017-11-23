(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import oseq.

Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "m >>= f" := (ssrfun.Option.bind f m) (at level 100).

(* -------------------------------------------------------------------- *)
Parameter var : countType.
Parameter mem : Type.

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
Canonical expr_eqType := EqType _ expr_eqMixin.

Definition eval (m : mem) (e : expr) :=
  match e return value with
  | EVar x => get m x
  | EInt i => i
  end.

Inductive cmd_name := ADDC | SUBC | MUL.

Definition cmd : Type := cmd_name * seq var * seq expr.

Parameter addc : int * int * bool -> int * bool.
Parameter subc : int * int * bool -> int * bool.
Parameter mul : int * int -> int * int.

Definition sem_addc_val (args : seq value) :=
  if args is [:: VInt x; VInt y; VBool c] then
     let: (z, c) := addc (x, y, c) in Some [:: VInt z; VBool c]
  else None.

Definition sem_subc_val (args : seq value) :=
  if args is [:: VInt x; VInt y; VBool c] then
     let: (z, c) := subc (x, y, c) in Some [:: VInt z; VBool c]
  else None.

Definition sem_mul_val (args : seq value) :=
  if args is [:: VInt x; VInt y] then
     let: (z, c) := mul (x, y) in Some [:: VInt z; VInt c]
  else None.

Definition sem_cmd (op : seq value -> option (seq value)) m outv inv :=
  if op [seq eval m x | x <- inv] is Some res then
    sets m outv res
  else None.

Definition semc (m : mem) (c : cmd) : option mem :=
  let: (c, outv, inv) := c in
  let: op :=
    match c with
    | ADDC => sem_addc_val
    | SUBC => sem_subc_val
    | MUL => sem_mul_val
    end
  in sem_cmd op m outv inv.

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

Definition sem_ad_in (xs : seq expr) (ad : arg_desc) : option expr :=
  match ad with
  | ADImplicit x => Some (EVar x)
  | ADExplicit n => onth xs n
  end.

Definition sem_ad_out (xs : seq expr) (ad : arg_desc) : option var :=
  match ad with
  | ADImplicit x => Some x
  | ADExplicit n =>
      if onth xs n is Some (EVar y) then Some y else None
  end.

(* -------------------------------------------------------------------- *)
Inductive register := R1 | R2 | R3.
Inductive flag     : Set := CF.
Inductive ireg     := IRReg of register | IRImm of int.

Axiom register_eqMixin : Equality.mixin_of register.
Canonical register_eqType := EqType _ register_eqMixin.

Axiom flag_eqMixin : Equality.mixin_of flag.
Canonical flag_eqType := EqType _ flag_eqMixin.

Axiom ireg_eqMixin : Equality.mixin_of ireg.
Canonical ireg_eqType := EqType _ ireg_eqMixin.

Inductive low_instr :=
| ADDC_lo of register & ireg
| SUBC_lo of register & int
| MUL_lo
.

Definition operands_of_instr (li: low_instr) : seq ireg :=
  match li with
  | ADDC_lo x y => [:: IRReg x ; y ]
  | SUBC_lo x y => [:: IRReg x ; IRImm y ]
  | MUL_lo => [::]
  end.

Record lomem := {
  lm_reg : register -> int;
  lm_fgs : flag -> bool;
}.

Definition eval_reg (m: lomem) (r: register) : int := lm_reg m r.
Definition eval_lit (m: lomem) (i: int) : int := i.
Definition eval_ireg  (m: lomem) (ir: ireg) : int := 
  match ir with
  | IRReg r => eval_reg m r
  | IRImm i => eval_lit m i
  end.

Definition eval_flag (m: lomem) (f: flag) : bool := lm_fgs m f.
Definition write_flag (m: lomem) (f: flag) (b: bool) :=
  {| lm_reg := lm_reg m ; lm_fgs := λ f', if f' == f then b else lm_fgs m f' |}.
Definition write_reg  (m: lomem) (r: register) (v: int) : lomem :=
  {| lm_reg := λ r', if r' == r then v else lm_reg m r'; lm_fgs := lm_fgs m |}.

Variant destination :=
| DReg of register
| DFlag of flag.

Axiom destination_eqMixin : Equality.mixin_of destination.
Canonical destination_eqType := EqType _ destination_eqMixin.

Parameter var_of_register : register -> var.
Parameter var_of_flag : flag -> var.

Axiom var_of_uniq :
  uniq
    (map var_of_register [:: R1 ; R2 ; R3 ] ++ map var_of_flag [:: CF ]).

Definition register_of_var (v: var) : option register :=
  if v == var_of_register R1 then Some R1 else
  if v == var_of_register R2 then Some R2 else
  if v == var_of_register R3 then Some R3 else
  None.

Lemma var_of_register_of_var v r :
  register_of_var v = Some r →
  var_of_register r = v.
Proof.
  rewrite /register_of_var.
  case: eqP; first by move => -> [] ->. move => _.
  case: eqP; first by move => -> [] ->. move => _.
  case: eqP; first by move => -> [] ->.
  done.
Qed.

Definition flag_of_var (v: var) : option flag :=
  if v == var_of_flag CF then Some CF else
  None.

Lemma var_of_flag_of_var v f :
  flag_of_var v = Some f →
  var_of_flag f = v.
Proof.
  by rewrite/flag_of_var; case: eqP => // -> [] <-.
Qed.

Definition compile_var (v: var) : option destination :=
  match register_of_var v with
  | Some r => Some (DReg r)
  | None =>
    match flag_of_var v with
    | Some f => Some (DFlag f)
    | None => None
    end
  end.

Definition vCF : var := var_of_flag CF.

Axiom compile_var_CF : compile_var vCF = Some (DFlag CF).
Axiom register_of_var_of_register :
  ∀ r, register_of_var (var_of_register r) = Some r.

Inductive lom_eqv (m : mem) (lom : lomem) :=
  | MEqv of
      (forall r, VInt  (lom.(lm_reg) r) = get m (var_of_register r))
    & (forall f, VBool (lom.(lm_fgs) f) = get m (var_of_flag f)).

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

Definition ireg_of_expr (arg: expr) : option ireg :=
  match arg with
  | EVar x => ssrfun.omap IRReg (register_of_var x)
  | EInt i => Some (IRImm i)
  end.

Definition typed_apply_ireg {T} (ty: arg_ty) (arg: ireg) : 
  (interp_ty ty → T) → option T :=
  match ty, arg with
  | TYVar, IRReg r => λ op, Some (op r)
  | TYLiteral, IRImm i => λ op, Some (op i)
  | TYVL, _ => λ op, Some (op arg)
  | _, _ => λ _, None
  end.

Fixpoint typed_apply_iregs (tys: seq arg_ty) (iregs: seq ireg)
  : interp_tys tys -> option low_instr :=
  match tys, iregs with
  | [::], [::] => Some
  | ty :: tys', ir :: iregs' => λ op,
                          @typed_apply_ireg _ ty ir op >>=
                          @typed_apply_iregs tys' iregs'
  | _, _ => λ _, None
  end.

Definition foon (tys: seq arg_ty) (args: seq expr) (op: interp_tys tys) : option low_instr :=
  if omap ireg_of_expr args is Some iregs then
    @typed_apply_iregs tys iregs op
  else None.

(* -------------------------------------------------------------------- *)
Definition cmd_name_of_loid (loid: low_instr) : cmd_name :=
  match loid with
  | ADDC_lo _ _ => ADDC
  | SUBC_lo _ _ => SUBC
  | MUL_lo => MUL
  end.

(* -------------------------------------------------------------------- *)
Definition wf_implicit (ad: arg_desc) : bool :=
  if ad is ADImplicit x then
    compile_var x != None
  else true.

Definition wf_sem (c: cmd_name) (tys: seq arg_ty) (sem: interp_tys tys) : Prop :=
  ∀ irs loid,
    typed_apply_iregs irs sem = Some loid →
    cmd_name_of_loid loid = c ∧
    operands_of_instr loid = irs.

(* -------------------------------------------------------------------- *)
Record instr_desc := {
  id_name : cmd_name;
  id_in   : seq arg_desc;
  id_out  : seq arg_desc;
  id_lo   : seq arg_ty;
  id_sem  : interp_tys id_lo;

  id_in_wf : all wf_implicit id_in;
  id_out_wf : all wf_implicit id_out;
  id_sem_wf: wf_sem id_name id_sem;
}.

Definition sem_id
  (m : mem) (id : instr_desc) (xs : seq expr) : option mem
:=
  let: inx  := omap (sem_ad_in xs) id.(id_in ) in
  let: outx := omap (sem_ad_out xs) id.(id_out) in

  if (inx, outx) is (Some inx, Some outx) then
    sem_cmd (match id.(id_name) with
    | ADDC => sem_addc_val
    | SUBC => sem_subc_val
    | MUL => sem_mul_val
    end) m outx inx
  else None.

(* -------------------------------------------------------------------- *)
Definition sem_lo (m : lomem) (i : low_instr) : lomem :=
  match i with
  | ADDC_lo r x =>
      let v1 := eval_reg  m r in
      let v2 := eval_ireg m x in
      let c  := eval_flag m CF in

      let: (res, cf) := addc (v1, v2, c) in

      write_reg (write_flag m CF cf) r res

  | SUBC_lo r x =>
      let v1 := eval_reg  m r in
      let v2 := eval_lit m x in
      let c  := eval_flag m CF in

      let: (res, cf) := subc (v1, v2, c) in

      write_reg (write_flag m CF cf) r res

  | MUL_lo =>
    let x1 := eval_reg m R1 in
    let x2 := eval_reg m R2 in

    let: (y1, y2) := mul (x1, x2) in

    write_reg (write_reg m R1 y1) R2 y2
  end.

(* -------------------------------------------------------------------- *)
Definition ADDC_desc : instr_desc. refine {|
  id_name := ADDC;
  id_in   := [:: ADExplicit 0; ADExplicit 1; ADImplicit vCF];
  id_out  := [:: ADExplicit 0; ADImplicit vCF];
  id_lo   := [:: TYVar; TYVL];
  id_sem  := ADDC_lo;
|}.
Proof.
  abstract by rewrite/= compile_var_CF.
  abstract by rewrite/= compile_var_CF.
  abstract by move => irs loid; case: irs => // [] // [] // x [] // y [] // [] <-.
Defined.

(* -------------------------------------------------------------------- *)
Definition SUBC_desc : instr_desc. refine {|
  id_name := SUBC;
  id_in   := [:: ADExplicit 0; ADExplicit 1; ADImplicit vCF];
  id_out  := [:: ADExplicit 0; ADImplicit vCF];
  id_lo   := [:: TYVar; TYLiteral];
  id_sem  := SUBC_lo;
|}.
Proof.
  abstract by rewrite/= compile_var_CF.
  abstract by rewrite/= compile_var_CF.
  abstract by case => // [] // [] // x [] // [] // n [] // loid [] <-.
Defined.

(* -------------------------------------------------------------------- *)
Definition MUL_desc : instr_desc. refine {|
  id_name := MUL;
  id_in   := [:: ADImplicit (var_of_register R1); ADImplicit (var_of_register R2)];
  id_out   := [:: ADImplicit (var_of_register R1); ADImplicit (var_of_register R2)];
  id_lo   := [::];
  id_sem  := MUL_lo;
|}.
Proof.
  abstract by rewrite/= /compile_var !register_of_var_of_register.
  abstract by rewrite/= /compile_var !register_of_var_of_register.
  abstract by move => [] // loid [] <-.
Defined.

(* -------------------------------------------------------------------- *)
Definition get_id (c : cmd_name) :=
  match c with
  | ADDC => ADDC_desc
  | SUBC => SUBC_desc
  | MUL => MUL_desc
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

(* --------------------------------------------------------------------
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
*)

(* -------------------------------------------------------------------- *)
Definition compile (c : cmd_name) (args : seq expr) :=
  let id := get_id c in foon args id.(id_sem).

(* -------------------------------------------------------------------- *)
Variant argument :=
| AReg of register
| AFlag of flag
| AInt of int.

Axiom argument_eqMixin : Equality.mixin_of argument.
Canonical argument_eqType := EqType argument argument_eqMixin.

Definition arg_of_dest (d: destination): argument :=
  match d with
  | DReg r => AReg r
  | DFlag f => AFlag f
  end.

Definition arg_of_ireg (i: ireg) : argument :=
  match i with
  | IRReg r => AReg r
  | IRImm i => AInt i
  end.

Definition sem_lo_ad_in (xs : seq ireg) (ad : arg_desc) : option argument :=
  match ad with
  | ADImplicit x => ssrfun.omap arg_of_dest (compile_var x)
  | ADExplicit n => ssrfun.omap arg_of_ireg (onth xs n)
  end.

Definition sem_lo_ad_out (xs : seq ireg) (ad : arg_desc) : option destination :=
  match ad with
  | ADImplicit x => compile_var x
  | ADExplicit n =>
      if onth xs n is Some (IRReg y) then Some (DReg y) else None
  end.

Definition eval_lo (m : lomem) (a : argument) : value :=
  match a with
  | AReg x => VInt (lm_reg m x)
  | AFlag f => VBool (lm_fgs m f)
  | AInt i => VInt i
  end.

Definition set_lo (d: destination) (v: value) (m: lomem) : option lomem :=
  match d, v with
  | DReg r, VInt i => Some (write_reg m r i)
  | DFlag f, VBool b => Some (write_flag m f b)
  | _, _ => None
  end.

Definition sets_lo (m : lomem) (x : seq destination) (v : seq value) :=
  if size x == size v then
    foldl (fun m xv => obind (set_lo xv.1 xv.2) m) (Some m) (zip x v)
  else None.

Definition sem_lo_cmd (op : seq value -> option (seq value)) m outv inv :=
  if op [seq eval_lo m x | x <- inv] is Some res then
    sets_lo m outv res
  else None.

Definition sem_lo_gen (m: lomem) (id: instr_desc) (li: low_instr) : option lomem :=
  let xs := operands_of_instr li in
  let: inx  := omap (sem_lo_ad_in xs) id.(id_in ) in
  let: outx := omap (sem_lo_ad_out xs) id.(id_out) in

  if (inx, outx) is (Some inx, Some outx) then
    sem_lo_cmd (match id.(id_name) with
    | ADDC => sem_addc_val
    | SUBC => sem_subc_val
    | MUL => sem_mul_val
    end) m outx inx
  else None.

Lemma eval_lo_arg_of_ireg m i :
  eval_lo m (arg_of_ireg i) = eval_ireg m i.
Proof. by case: i. Qed.

Definition evalrw := (compile_var_CF, eval_lo_arg_of_ireg).

Lemma sem_lo_gen_correct m loid :
  sem_lo_gen m (get_id (cmd_name_of_loid loid)) loid = Some (sem_lo m loid).
Proof.
case: loid.
- move=> r i; rewrite /sem_lo_gen /= ?evalrw /sem_lo_cmd /= ?evalrw.
  by case: addc.
- move=> r i; rewrite /sem_lo_gen /= ?evalrw /sem_lo_cmd /= ?evalrw.
  by case: subc.
- rewrite /sem_lo_gen /= /compile_var ! register_of_var_of_register /= /sem_lo_cmd /=.
  by case: mul.
Qed.

(* -------------------------------------------------------------------- *)
Definition argument_of_expr (e : expr) : option argument :=
  match e with
  | EVar x => ssrfun.omap arg_of_dest (compile_var x)
  | EInt i => Some (AInt i)
  end.

Lemma toto_in ads vs args irs m lom :
  lom_eqv m lom →
  all wf_implicit ads →
  omap ireg_of_expr vs = Some irs →
  omap (sem_ad_in vs) ads = Some args →
  ∃ loargs, omap (sem_lo_ad_in irs) ads = Some loargs ∧
  map (eval_lo lom) loargs = map (eval m) args.
Proof.
  move => eqm hwf hirs.
  elim: ads args hwf.
  - by move => args _ [] <-; exists [::].
  move => ad ads ih args' h; rewrite /= in h; case/andP: h => hwf hwf'.
  case/omap_consI => arg [] args [] -> ha has.
  case: (ih _ hwf' has) => {ih} loargs [hlo hlo'].
  case: ad ha hwf.
  + move => x /= [] ?; subst arg.
    case hd: compile_var => [ d | ] // _.
    exists (arg_of_dest d :: loargs); split; first by rewrite /= hlo.
    rewrite/=; f_equal => //.
    case: eqm => hr hf.
    move: hd; rewrite/compile_var.
    case eq1: register_of_var => [ r | ].
    * by case => <- /=; rewrite hr (var_of_register_of_var eq1).
    case eq2: flag_of_var => [ f | ] //.
    by case => <- /=; rewrite hf (var_of_flag_of_var eq2).
  move => /= x /onthP - /(_ (EInt 0)) /andP [] hx /eqP hx' _; subst arg.
  rewrite (onth_omap_size (EInt 0) hirs hx) -/(ireg_of_expr _).
  rewrite (onth_omap x hirs) -/ireg_of_expr (onth_nth_size (EInt 0) hx) /=.
  
  have : onth vs x = Some (nth (EInt 0) vs x).
  apply: onth_nth_size.

  Search _ (Option.apply).
  have : onth irs x = (onth vs x >>= ireg_of_expr) by exact: (onth_omap x hirs).
  move => ->.
  rewrite (omap_size hirs) in hx.
  rewrite (onth_nth_size (IRReg R1) hx) /= hlo /=.
  eexists; split; first by reflexivity.
  rewrite /=; f_equal => //.
  rewrite eval_lo_arg_of_ireg /=.
  apply/eqP; rewrite oseqP; apply /eqP => /=.
  rewrite oeq => //=.
  f_equal => //.
  by apply/eqP; rewrite -oseqP; apply/eqP.

  rewrite /=. f_equal => //.
  have : ireg_of_expr arg = Some (nth (IRReg R1) irs x).
  rewrite -oeq -hx'.
  admit. (* onth / omap *)
  case: nth {hx'} arg => [ r | i ] [] //=.
  move => s; case: eqm => eqm _.
  by case eq1: register_of_var => [ y | ] // [] <-; rewrite eqm (var_of_register_of_var eq1).
  by move => s; case: register_of_var.
  by move => ? [] ->.
Qed.

Lemma toto_out ads vs out irs m1 lom1 outv m2 :
  lom_eqv m1 lom1 →
  all wf_implicit ads →
  oseq (map ireg_of_expr vs) = Some irs →
  oseq [seq sem_ad_out ad vs | ad <- ads ] = Some out →
  sets m1 out outv = Some m2 →
  ∃ outx, oseq [seq sem_lo_ad_out ad irs | ad <- ads ] = Some outx ∧
  ∃ lom2 : lomem, sets_lo lom1 outx outv = Some lom2 ∧ lom_eqv m2 lom2.
Proof.
Admitted.

(* -------------------------------------------------------------------- *)
Theorem L2 c vs m1 m2 loid lom1:
     compile c vs = Some loid
  -> sem_id m1 (get_id c) vs = Some m2
  -> lom_eqv m1 lom1
  -> exists lom2, sem_lo_gen lom1 (get_id c) loid = Some lom2
  /\ lom_eqv m2 lom2.
Proof.
rewrite /compile /sem_id => h.
case E1: (oseq _) => [args|//].
case E2: (oseq _) => [out|//].
rewrite get_id_ok; set op := (X in sem_cmd X).
rewrite /sem_cmd; case E3: (op _) => [outv|//].
rewrite /sem_lo_gen.
move: h. rewrite /foon. case h: oseq => // [irs] hirs.
rewrite (proj2 (id_sem_wf hirs)).
rewrite /sem_lo_cmd.
rewrite get_id_ok -/op.
move => hsets heqm.
have [ inx [ E4 E5 ] ] := toto_in heqm (id_in_wf _) h E1. rewrite E4.
have [ outx [ E6 [ lom2 [ E7 E8 ] ] ] ] := toto_out heqm (id_out_wf _) h E2 hsets.
rewrite E6 E5 E3. eauto.
Qed.

Lemma compile_cmd_name c vs loid :
  compile c vs = Some loid →
  cmd_name_of_loid loid = c.
Proof.
  rewrite /compile /foon.
  case: oseq => // irs h.
  have := @id_sem_wf (get_id c) irs loid h.
  rewrite get_id_ok.
  by case.
Qed.

Theorem L3 c vs m1 m2 loid lom :
     compile c vs = Some loid
  -> sem_id m1 (get_id c) vs = Some m2
  -> lom_eqv m1 lom
  -> lom_eqv m2 (sem_lo lom loid).
Proof.
  move => hc.
  move/L2: (hc) => h /h {h} h /h {h} [lom'] [].
  by rewrite -(compile_cmd_name hc) sem_lo_gen_correct => - [] <-.
Qed.

(* --------------------------------------------------------------------- *)
Lemma L' id vs args loid :
     foon vs (id_sem id) = Some loid
  -> oseq [seq sem_ad_in ad vs | ad <- id_in id] = Some args
  ->   oseq [seq sem_lo_ad_in ad (operands_of_instr loid) | ad <- id_in id]
     = oseq [seq argument_of_expr e | e <- args].
Proof.
case: id => c iin _ ilo isem /= h.
rewrite (rwP eqP) oseqP -(rwP eqP) => eq; congr oseq.
move: h. rewrite /foon.
elim: iin args eq => [|iin1 iin ih] [|arg args] //=.
case=> eq1 /ih {ih iin} ->; congr (_ :: _) => {args}.
elim: ilo isem h eq1 => /=.
- case: vs => // ? []

have :
  operands_of_instr loid = oseq (map argument_of_expr vs).
elim: 
rewrite/operands_of_instr.


