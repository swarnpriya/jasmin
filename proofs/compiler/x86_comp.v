(* -------------------------------------------------------------------- *)
Require Import Utf8.
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import xseq expr linear compiler_util.
(* ------- *) Require Import low_memory x86_sem.
              Require Import oseq.
Import sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
(* Compilation of variables                                             *) 
Variant destination :=
| DAddr of address
| DReg  of register
| DFlag of rflag.

Axiom destination_eqMixin : Equality.mixin_of destination. 
Canonical destination_eqType := EqType destination destination_eqMixin.

Definition string_of_register r :=
  match r with
  | RAX => "RAX"
  | RCX => "RCX"
  | RDX => "RDX"
  | RBX => "RBX"
  | RSP => "RSP"
  | RBP => "RBP"
  | RSI => "RSI"
  | RDI => "RDI"
  | R8  => "R8"
  | R9  => "R9"
  | R10 => "R10"
  | R11 => "R11"
  | R12 => "R12"
  | R13 => "R13"
  | R14 => "R14"
  | R15 => "R15"
  end%string.

Definition string_of_rflag (rf : rflag) : string :=
  match rf with
 | CF => "CF"
 | PF => "PF"
 | ZF => "ZF"
 | SF => "SF"
 | OF => "OF"
 | DF => "DF"
 end%string.

Definition regs_strings :=
  Eval compute in [seq (string_of_register x, x) | x <- registers].

Lemma regs_stringsE : regs_strings =
  [seq (string_of_register x, x) | x <- registers].
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Definition rflags_strings :=
  Eval compute in [seq (string_of_rflag x, x) | x <- rflags].

Lemma rflags_stringsE : rflags_strings =
  [seq (string_of_rflag x, x) | x <- rflags].
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Definition reg_of_string (s : string) :=
  assoc regs_strings s.

(* -------------------------------------------------------------------- *)
Definition rflag_of_string (s : string) :=
  assoc rflags_strings s.

(* -------------------------------------------------------------------- *)
Lemma rflag_of_stringK : pcancel string_of_rflag rflag_of_string.
Proof. by case. Qed.

Lemma reg_of_stringK : pcancel string_of_register reg_of_string.
Proof. by case. Qed.

Lemma inj_string_of_rflag : injective string_of_rflag.
Proof. by apply: (pcan_inj rflag_of_stringK). Qed.

Lemma inj_string_of_register : injective string_of_register.
Proof. by apply: (pcan_inj reg_of_stringK). Qed.

(* -------------------------------------------------------------------- *)
Lemma inj_reg_of_string s1 s2 r :
     reg_of_string s1 = Some r
  -> reg_of_string s2 = Some r
  -> s1 = s2.
Proof. by rewrite /reg_of_string !regs_stringsE; apply: inj_assoc. Qed.

(* -------------------------------------------------------------------- *)
Lemma inj_rflag_of_string s1 s2 rf :
     rflag_of_string s1 = Some rf
  -> rflag_of_string s2 = Some rf
  -> s1 = s2.
Proof. by rewrite /rflag_of_string !rflags_stringsE; apply: inj_assoc. Qed.

(* -------------------------------------------------------------------- *)

Definition var_of_register r := 
  {| vtype := sword; vname := string_of_register r |}. 

Definition var_of_flag f := 
  {| vtype := sbool; vname := string_of_rflag f |}. 

Lemma var_of_register_inj x y :
  var_of_register x = var_of_register y →
  x = y.
Proof. by move=> [];apply inj_string_of_register. Qed.

Lemma var_of_flag_inj x y : 
  var_of_flag x = var_of_flag y →
  x = y.
Proof. by move=> [];apply inj_string_of_rflag. Qed.

Lemma var_of_register_var_of_flag r f :
  ¬ var_of_register r = var_of_flag f.
Proof. by case: r;case: f. Qed.

Definition register_of_var (v:var) : option register := 
  if v.(vtype) == sword then reg_of_string v.(vname)
  else None.

Lemma var_of_register_of_var v r :
  register_of_var v = Some r →
  var_of_register r = v.
Proof.
  rewrite /register_of_var /var_of_register;case:ifP => //.
  case: v => [vt vn] /= /eqP -> H;apply f_equal.
  by apply: inj_reg_of_string H; apply reg_of_stringK.
Qed.

Definition flag_of_var (v: var) : option rflag :=
  if v.(vtype) == sbool then rflag_of_string v.(vname)
  else None.

Lemma var_of_flag_of_var v f :
  flag_of_var v = Some f →
  var_of_flag f = v.
Proof.
  rewrite /flag_of_var /var_of_flag;case:ifP => //.
  case: v => [vt vn] /= /eqP -> H; apply f_equal.
  by apply: inj_rflag_of_string H; apply rflag_of_stringK.
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

Lemma register_of_var_of_register r :
  register_of_var (var_of_register r) = Some r.
Proof.
  rewrite /register_of_var /var_of_register /=.
  by apply reg_of_stringK.
Qed.

(* -------------------------------------------------------------------- *)
Variant arg_ty := TYcondt | TYoprd | TYreg | TYireg | TYimm.

Scheme Equality for arg_ty.

Definition arg_ty_eqMixin := comparableClass arg_ty_eq_dec.
Canonical arg_ty_eqType := EqType arg_ty arg_ty_eqMixin.

Definition interp_ty (ty : arg_ty) : Type :=
  match ty with
  | TYcondt => condt
  | TYoprd  => oprd
  | TYreg   => register
  | TYireg  => ireg
  | TYimm => word
  end.

Fixpoint interp_tys (tys : seq arg_ty) :=
  if tys is ty :: tys then
    interp_ty ty -> interp_tys tys
  else asm.

Fixpoint tys_t_rec (ty: Type) tys : Type :=
  match tys with
  | [::] => ty
  | ty' :: tys' => tys_t_rec (ty * interp_ty ty') tys'
  end.

Definition tys_tuple (tys: seq arg_ty) : Type :=
  match tys with
  | [::] => unit
  | ty :: tys => tys_t_rec (interp_ty ty) tys
  end.

Variant garg := Gcondt of condt | Goprd of oprd.

Definition typed_apply_garg {T} (ty: arg_ty) (arg: garg) :
  (interp_ty ty → T) → option T :=
    match ty, arg return (interp_ty ty → T) → option T with
    | TYcondt, Gcondt c => λ op, Some (op c)
    | TYoprd, Goprd x => λ op, Some (op x)
    | TYreg, Goprd (Reg_op r) => λ op, Some (op r)
    | TYireg, Goprd (Reg_op r)=> λ op, Some (op (Reg_ir r))
    | TYireg, Goprd (Imm_op w)=> λ op, Some (op (Imm_ir w))
    | _, _ => λ _, None
    end.

Fixpoint typed_apply_gargs (tys: seq arg_ty) (iregs: seq garg)
  : interp_tys tys -> option asm :=
  match tys, iregs with
  | [::], [::] => Some
  | ty :: tys', ir :: iregs' => λ op,
                          (@typed_apply_garg _ ty ir op >>=
                           @typed_apply_gargs tys' iregs')%O
  | _, _ => λ _, None
  end.

(* -------------------------------------------------------------------- *)

(* Describe where to recover the argument in the intermediate language *)
Variant arg_desc :=
| ADImplicit of var
| ADExplicit of nat & option var. 
 (* [ADExplicit i (Some x)] in this case the ith argument should be the variable x (see SHL) *)

Definition arg_desc_beq ad1 ad2 := 
  match ad1, ad2 with
  | ADImplicit x1, ADImplicit x2 => x1 == x2
  | ADExplicit i1 ox1, ADExplicit i2 ox2 => (i1 == i2) && (ox1 == ox2)
  | _, _ => false
  end.

Lemma arg_desc_beq_axiom : Equality.axiom arg_desc_beq.
Proof.
  move=> [x1 | i1 ox1] [x2 | i2 ox2] //=.
  + by case: (x1 =P x2) => [-> | neq ];constructor;congruence.
  + by constructor.
  + by constructor.
  case: (i1 =P i2) => [-> | neq ];last by constructor;congruence.
  by case: (_ =P _) => [-> | neq ];constructor;congruence.
Qed.

Definition arg_desc_eqMixin := Equality.Mixin arg_desc_beq_axiom .
Canonical arg_desc_eqType := EqType _ arg_desc_eqMixin.

Definition wf_implicit (ad: arg_desc) : bool :=
  if ad is ADImplicit x then
    compile_var x != None
  else true.

(* -------------------------------------------------------------------- *)
(* Generated ASM semantics                                              *)

Variant argument :=
 | Aflag  of rflag
 | Aoprd  of oprd
 | Acondt of condt.

Axiom argument_eqMixin : Equality.mixin_of argument.
Canonical argument_eqType := EqType argument argument_eqMixin.

Definition arg_of_dest (d: destination): argument :=
  match d with
  | DAddr addr => Aoprd (Adr_op addr)
  | DReg  r    => Aoprd (Reg_op r)
  | DFlag f    => Aflag f
  end.

Definition arg_of_garg (i: garg) : argument :=
  match i with
  | Gcondt c => Acondt c
  | Goprd o => Aoprd o
  end.

Definition low_sem_ad_in (xs : seq garg) (ad : arg_desc) : option argument :=
  match ad with
  | ADImplicit x => ssrfun.omap arg_of_dest (compile_var x)
  | ADExplicit n None => ssrfun.omap arg_of_garg (onth xs n)
  | ADExplicit n (Some x) =>
    let r1 := ssrfun.omap arg_of_garg (onth xs n) in
    let r2 := ssrfun.omap arg_of_dest (compile_var x) in
    if r1 == r2 then r1 else None
  end.

Definition low_sem_ad_out (xs : seq garg) (ad : arg_desc) : option destination :=
  match ad with
  | ADImplicit x => compile_var x
  | ADExplicit n None =>
    onth xs n >>= λ g,
    match g with
    | Goprd (Reg_op r) => Some (DReg r)
    | Goprd (Adr_op a) => Some (DAddr a)
    | _ => None
    end
  | _ => None
  end%O.

Definition st_get_rflag_lax (f: rflag) (m: x86_mem) : value :=
  if m.(xrf) f is Def b then Vbool b else Vundef sbool.

Definition eval_low gd (m : x86_mem) (a : argument) : exec value :=
  match a with
  | Aflag f => ok (st_get_rflag_lax f m)
  | Aoprd o => read_oprd gd o m >>= λ w, ok (Vword w)
  | Acondt c => eval_cond c m.(xrf) >>= λ b, ok (Vbool b)
  end.

Definition set_low (d: destination) (v: value) (m: x86_mem) : result _ x86_mem :=
  match d, v with
  | DAddr a, Vword w =>
    let x := decode_addr m a in
    mem_write_mem x w m
  | DReg r, Vword w => ok (mem_write_reg r w m)
  | DFlag f, Vbool b => ok (mem_set_rflags f b m)
  | DFlag f, Vundef sbool => ok (mem_unset_rflags f m)
  | _, _ => type_error
  end.

Definition sets_low (m : x86_mem) (x : seq destination) (v : seq value) :=
  if size x == size v then
    foldl (fun m xv => Result.bind (set_low xv.1 xv.2) m) (ok m) (zip x v)
  else type_error.

Definition low_sem_aux (gd: glob_defs) (m: x86_mem) (op: sopn)
           (outx inx: seq arg_desc) (xs: seq garg) : exec x86_mem :=
  let inx := omap (low_sem_ad_in xs) inx in
  let outx := omap (low_sem_ad_out xs) outx in
  if (inx, outx) is (Some inx, Some outx) then
    mapM (eval_low gd m) inx >>= exec_sopn op >>= sets_low m outx
  else type_error.

(* -------------------------------------------------------------------- *)
Definition mk_garg ty : interp_ty ty -> garg := 
  match ty with
  | TYcondt => Gcondt 
  | TYoprd => Goprd
  | TYreg  => fun r => Goprd (Reg_op r)
  | TYireg => fun ir => Goprd (match ir with Imm_ir i => Imm_op i | Reg_ir r => Reg_op r end)
  | TYimm => fun i => Goprd (Imm_op i)
  end.

Fixpoint seq_of_tys_t_rec ty tys : (ty -> list garg) -> tys_t_rec ty tys -> list garg := 
  match tys with
  | [::] => fun k t => k t 
  | ty'::tys => fun k => @seq_of_tys_t_rec (ty * interp_ty ty')%type tys 
     (fun (p:ty * interp_ty ty') => rcons (k p.1) (@mk_garg ty' p.2))
  end.

Definition seq_of_tys_tuple tys : tys_tuple tys -> list garg := 
  match tys with
  | [::] => fun tt => [::]
  | ty::tys => @seq_of_tys_t_rec (interp_ty ty) tys (fun a => [::@mk_garg ty a])
  end.

Fixpoint gen_sem_correct tys id_name id_out id_in args  : interp_tys tys -> Prop := 
  match tys with
  | [::] => fun asm => 
    ∀ gd m m',
       low_sem_aux gd m id_name id_out id_in args = ok m' ->
       eval_instr_mem gd asm m = ok m'
  | ty::tys => fun asm => 
    forall (x:interp_ty ty), @gen_sem_correct tys id_name id_out id_in (args ++ [::@mk_garg ty x]) (asm x)
  end.

Arguments gen_sem_correct : clear implicits.

(*

Definition gen_sem_correct (id_tys: seq arg_ty) id_name id_out id_in id_instr := 
   
  ∀ gd args m m',
      low_sem_aux gd m id_name id_out id_in (@seq_of_tys_tuple id_tys args) = ok m' ->
       eval_instr_mem gd (typed_apply_gargs id_instr (@seq_of_tys_tuple id_tys args) id_instr) m = ok m'.

*)

Record instr_desc := mk_instr_desc {
  id_name : sopn;
  id_out  : seq arg_desc;
  id_in   : seq arg_desc;
  id_tys  : seq arg_ty;
  id_instr: interp_tys id_tys;

  (* FIXME : Add the functionnal semantic of the operator in the record,
             this require to the have its syntatic type *)
  id_gen_sem : gen_sem_correct id_tys id_name id_out id_in [::] id_instr;
  id_in_wf   : all wf_implicit id_in;
  id_out_wf  : all wf_implicit id_out;
}.

Definition low_sem gd m (id: instr_desc) (gargs: seq garg) : x86_result :=
  low_sem_aux gd m id.(id_name) id.(id_out) id.(id_in) gargs.

(* -------------------------------------------------------------------- *)
(* Generated mixed semantics                                            *)

Definition is_var (x:var) e := 
  match e with
  | Pvar x' => x == x'
  | _ => false
  end.

Definition mixed_sem_ad_in (xs : seq pexpr) (ad : arg_desc) : option pexpr :=
  match ad with
  | ADImplicit x => Some (Pvar (VarI x xH)) 
  | ADExplicit n None => onth xs n
  | ADExplicit n (Some x) =>
    onth xs n >>= fun e => if is_var x e then Some e else None
  end%O.

Definition lval_of_pexpr e := 
  match e with
  | Pvar v    => Some (Lvar v)
  | Pload x e => Some (Lmem x e)
  | _         => None
  end.

Definition mixed_sem_ad_out (xs : seq pexpr) (ad : arg_desc) : option lval :=
  match ad with
  | ADImplicit x => Some (Lvar (VarI x xH))
  | ADExplicit n None =>
    onth xs n >>= lval_of_pexpr
  | _ => None
  end%O.

Definition mixed_sem gd m (id : instr_desc) (xs : seq pexpr) :=
  let: inx  := omap (mixed_sem_ad_in xs) id.(id_in ) in
  let: outx := omap (mixed_sem_ad_out xs) id.(id_out) in
  if (inx, outx) is (Some inx, Some outx) then
    sem_sopn gd id.(id_name) m outx inx
  else type_error.

(* -------------------------------------------------------------------- *)
(* Definitions of descriptors                                           *)

Definition implicit_flags := 
  map (ADImplicit \o var_of_flag) [::OF; CF; SF; PF; ZF].

Definition implicit_flags_noCF := 
  map (ADImplicit \o var_of_flag) [::OF; SF; PF; ZF].

Local Coercion E n := ADExplicit n None.
Local Coercion F f := ADImplicit (var_of_flag f).
Local Coercion R f := ADImplicit (var_of_register f).

Notation make_instr_desc gen_sem := (mk_instr_desc gen_sem erefl erefl).

(* ----------------------------------------------------------------------------- *)
Lemma MOV_gsc : 
  gen_sem_correct [:: TYoprd; TYoprd] Ox86_MOV [:: E 0] [:: E 1] [::] MOV.
Proof.
  move=> [] // => [ x | x] y gd m m';rewrite /low_sem_aux /= /eval_MOV /=;
  by t_xrbindP => ???? -> <- <- [<-] <-.   
Qed.

Definition MOV_desc := make_instr_desc MOV_gsc.

(* ----------------------------------------------------------------------------- *)

Lemma RegMap_set_id rm x : rm = RegMap.set rm x (rm x).
Proof. by apply /ffunP;case;rewrite !ffunE;(case:eqP => [<- | ?]). Qed.

Lemma write_mem_id mem a vx :
  Memory.read_mem mem a = ok vx ->
  Memory.write_mem mem a vx = ok mem.
Proof.
  move=> Ha;have Hval: Memory.valid_addr mem a.
  + by apply /Memory.readV;exists vx.
  move: (Hval) => /Memory.writeV -/(_ vx) [m1] /= H;rewrite H;f_equal.
  apply Memory.eq_memP => w.
  case: (a =P w) => [<- | neq].
  + by have := Memory.writeP_eq vx Hval; rewrite Ha H /= => ->.
  by have := Memory.writeP_neq vx Hval neq; rewrite H /= => ->.
Qed.

Lemma CMOVcc_gsc : 
  gen_sem_correct [:: TYcondt; TYoprd; TYoprd]
     Ox86_CMOVcc [:: E 1] [:: E 0; E 2; E 1] [::] CMOVcc.
Proof.
  move=> ct [] // => [x | x] y gd m m';
  rewrite /low_sem_aux /= /= /eval_CMOVcc /eval_MOV /=.
  + t_xrbindP => ??? b -> <- ?? vy Hy <- <- <- /=. 
    case:ifP => ? -[<-] [<-];rewrite ?Hy //.
    by rewrite /mem_write_reg /=; f_equal;rewrite -RegMap_set_id;case:(m).
  t_xrbindP => ??? b -> <- ?? vy Hy <- ?? vx Hx <- <- <- <- /=. 
  case:ifP => ? -[<-].
  + by rewrite /sets_low /= Hy.
  rewrite /sets_low /= /mem_write_mem => {Hy}.
  case: m (decode_addr _ _) Hx => xmem xreg xrf /= a.
  by move=> /write_mem_id -> //.
Qed.

Definition CMOVcc_desc := make_instr_desc CMOVcc_gsc.

(* ----------------------------------------------------------------------------- *)

Ltac update_set := 
  by rewrite /sets_low /= /mem_update_rflags /mem_unset_rflags /mem_set_rflags 
             /mem_write_reg /=;
     repeat f_equal; apply /ffunP; case; rewrite !ffunE.

Lemma ADD_gsc :
   gen_sem_correct [:: TYoprd; TYoprd] Ox86_ADD
     (implicit_flags ++ [:: E 0]) 
     [:: E 0; E 1] [::] ADD.
Proof.
  move=> [] // => [ x | x] y gd m m'; rewrite /low_sem_aux /= /eval_ADD /=.
  + by t_xrbindP => vs ??? vy -> <- <- <- [<-] [<-]; update_set.
  by t_xrbindP => vs ??? -> <- ?? vy -> <- <- <-[<-] <- /=; update_set.
Qed.

Definition ADD_desc := make_instr_desc ADD_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma SUB_gsc : 
   gen_sem_correct [:: TYoprd; TYoprd] Ox86_SUB
      (implicit_flags ++ [:: E 0]) [:: E 0; E 1] [::] SUB.
Proof.
  move=> [] // => [ x | x] y gd m m'; rewrite /low_sem_aux /= /eval_SUB /=.
  + by t_xrbindP => vs ??? vy -> <- <- <- [<-] [<-]; update_set.
  by t_xrbindP => vs ??? -> <- ?? vy -> <- <- <- [<-] <- /=; update_set.
Qed.

Definition SUB_desc := make_instr_desc SUB_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma MUL_gsc :
  gen_sem_correct [:: TYoprd] Ox86_MUL
      (implicit_flags ++ [:: R RDX; R RAX])
      [:: R RAX; E 0] [::] MUL.
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= /eval_MUL => x gd m m'.
  by t_xrbindP => vs ? ? ? vy -> <- <- <- /= [<-] [<-] /=; update_set.
Qed.

Definition MUL_desc := make_instr_desc MUL_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma IMUL_gsc :
  gen_sem_correct [:: TYoprd ] Ox86_IMUL (implicit_flags ++ [:: R RDX; R RAX])
                   [:: R RAX; E 0] [::] (λ x, IMUL x None).
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= => x gd m m'.
  by t_xrbindP => vs ? ? ? vy -> <- <- <- /= [<-] [<-] /=; update_set.
Qed.

Definition IMUL_desc   := make_instr_desc IMUL_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma IMUL64_gsc :
  gen_sem_correct [:: TYoprd ; TYoprd] Ox86_IMUL64
                   (implicit_flags ++ [:: E 0]) [:: E 0; E 1] [::]
                   (λ x y, IMUL x (Some (y, None))).
Proof.
  rewrite /gen_sem_correct /low_sem_aux /=.
  case => // x y gd m m' /=.
  + t_xrbindP => vs ? ? ? vy -> <- <- <-.
    t_xrbindP => vx [<-] ? [<-] [<-] [<-] /=; update_set.
  t_xrbindP => vs ? ? ? -> <- ? ? ? -> <- <- <-.
  t_xrbindP => ? [<-] ? [<-] [<-] <-.
  update_set.
Qed.

Definition IMUL64_desc := make_instr_desc IMUL64_gsc.

Lemma IMUL64imm_gsc :
  gen_sem_correct [:: TYoprd ; TYoprd ; TYimm] Ox86_IMUL64imm
                   (implicit_flags ++ [:: E 0]) [:: E 1; E 2] [::]
    (λ (x y : interp_ty TYoprd) (z : interp_ty TYimm), IMUL x (Some (y, Some z))).
Proof.
  rewrite /gen_sem_correct /low_sem_aux /=.
  case => // d x y gd m m' /=.
  + t_xrbindP => vs ? ? ? -> <- <-.
    t_xrbindP => ? [<-] ? [<-] [<-] [<-] /=; update_set.
  t_xrbindP => vs ? ? ? -> <- <-.
  t_xrbindP => ? [<-] ? [<-] [<-] <-.
  update_set.
Qed.

Definition IMUL64imm_desc := make_instr_desc IMUL64imm_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma DIV_gsc : 
  gen_sem_correct [:: TYoprd] Ox86_DIV
      (implicit_flags ++ [:: R RAX; R RDX])
      [:: R RDX; R RAX; E 0] [::] DIV.
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= /eval_DIV /x86_div => x gd m m'.
  t_xrbindP => vs ? ? ? ? vy -> <- <- <- <- /=.
  by case: ifPn => //= ? [<-] /= [<-]; update_set.
Qed.

Definition DIV_desc := make_instr_desc DIV_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma IDIV_gsc :
  gen_sem_correct [:: TYoprd] Ox86_IDIV
      (implicit_flags ++ [:: R RAX; R RDX])
      [:: R RDX; R RAX; E 0] [::] IDIV.
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= /eval_IDIV /x86_idiv => x gd m m'.
  t_xrbindP => vs ? ? ? ? vy -> <- <- <- <- /=.
  by case: ifPn => //= ? [<-] /= [<-]; update_set.
Qed.

Definition IDIV_desc := make_instr_desc IDIV_gsc.
          
(* ----------------------------------------------------------------------------- *)
Lemma ADC_gsc : 
   gen_sem_correct [:: TYoprd; TYoprd] Ox86_ADC
       (implicit_flags ++ [:: E 0]) 
       [:: E 0; E 1; F CF] [::] ADC.
Proof.
  move=> [] // => [ x | x] y gd m m'; rewrite /low_sem_aux /= /eval_ADC /=. 
  + t_xrbindP => vs ??? vy -> <- <- <- /=.
    rewrite /st_get_rflag_lax /st_get_rflag.
    by case: ((xrf m) CF) => //= b [<-] /= [<-]; update_set.
  t_xrbindP => vs ??? -> <- ?? vy -> <- <- <- /=.
  rewrite /st_get_rflag_lax /st_get_rflag.
  by case: ((xrf m) CF) => //= b [<-] /= <-; update_set.
Qed.

Definition ADC_desc := make_instr_desc ADC_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma SBB_gsc : 
   gen_sem_correct [:: TYoprd; TYoprd] Ox86_SBB
       (implicit_flags ++ [:: E 0]) 
       [:: E 0; E 1; F CF] [::] SBB.
Proof.
  move=> [] // => [ x | x] y gd m m'; rewrite /low_sem_aux /= /eval_SBB /=. 
  + t_xrbindP => vs ??? vy -> <- <- <- /=.
    rewrite /st_get_rflag_lax /st_get_rflag.
    by case: ((xrf m) CF) => //= b [<-] /= [<-]; update_set.
  t_xrbindP => vs ??? -> <- ?? vy -> <- <- <- /=.
  rewrite /st_get_rflag_lax /st_get_rflag.
  by case: ((xrf m) CF) => //= b [<-] /= <-; update_set.
Qed.

Definition SBB_desc := make_instr_desc SBB_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma NEG_gsc :
  gen_sem_correct [:: TYoprd] Ox86_NEG
     (implicit_flags ++ [:: E 0])
     [:: E 0] [::] NEG.
Proof.
  move=> [] // => [ x | x ] gd m m';rewrite /low_sem_aux /= /eval_NEG /=. 
  + by move=> [<-];update_set.
  t_xrbindP => ???? -> <- <- /= [<-] <-;update_set.
Qed.

Definition NEG_desc := make_instr_desc NEG_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma INC_gsc :
  gen_sem_correct [:: TYoprd] Ox86_INC
     (implicit_flags_noCF ++ [:: E 0])
     [:: E 0] [::] INC.
Proof.
  move=> [] // => [ x | x ] gd m m'; rewrite /low_sem_aux /= /eval_INC /=. 
  + by move=> [<-]; update_set.
  by t_xrbindP => ???? -> <- <- /= [<-] <-; update_set.
Qed.

Definition INC_desc := make_instr_desc INC_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma DEC_gsc :
  gen_sem_correct [:: TYoprd] Ox86_DEC
     (implicit_flags_noCF ++ [:: E 0])
     [:: E 0] [::] DEC.
Proof.
  move=> [] // => [ x | x ] gd m m';rewrite /low_sem_aux /= /eval_DEC /=. 
  + by move=> [<-]; update_set.
  by t_xrbindP => ???? -> <- <- /= [<-] <-; update_set.
Qed.

Definition DEC_desc := make_instr_desc DEC_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma SETcc_gsc :
  gen_sem_correct [:: TYcondt; TYoprd] Ox86_SETcc
     [:: E 1]
     [:: E 0] [::] SETcc.
Proof.
  move=> ct [] // => [ x | x] gd m m';rewrite /low_sem_aux /= /eval_SETcc /=;
   by t_xrbindP => ???? -> <- <- /= [<-] [<-].
Qed.

Definition SETcc_desc := make_instr_desc SETcc_gsc.

(* ----------------------------------------------------------------------------- *)

Definition scale_of_z z :=
  match z with
  | 1 => Scale1
  | 2 => Scale2
  | 4 => Scale4
  | 8 => Scale8
  | _ => Scale1 
  end%Z.

Definition mk_LEA (dest:register) (disp:word) (base:ireg) (scale:word) (offset:ireg) := 
  let addr := 
    let (disp, base) := 
      match base with
      | Reg_ir r => (disp, Some r)
      | Imm_ir w => (I64.add disp w, None)
      end in
    let (disp, offset) := 
      match offset with
      | Reg_ir r => (disp, Some r)
      | Imm_ir w => (I64.add disp (I64.mul scale w), None) 
      end in
    let scale := scale_of_z scale in
    {| ad_disp := disp; ad_base := base; ad_scale := scale; ad_offset := offset |} in
  LEA dest (Adr_op addr).

Lemma read_oprd_ireg gd y m : 
  read_oprd gd match y with
               | Imm_ir i => Imm_op i
               | Reg_ir r => Reg_op r
               end m = ok (read_ireg y m).
Proof. by case: y => //. Qed.

Definition I64_rw := (I64.mul_zero, I64.add_zero, I64.repr_unsigned, I64.add_assoc, I64.add_zero_l).

Lemma check_scale_of (scale:word) : check_scale scale -> scale = scale_of_z scale.
Proof.
  move=> H;apply /ueqP;apply /eqP.
  by case /orP: H => [ /orP [ /orP [] /eqP -> | /eqP -> ] | /eqP ->].
Qed.

Lemma LEA_gsc :
  gen_sem_correct [:: TYreg; TYimm; TYireg; TYimm; TYireg] Ox86_LEA
     [:: E 0]
     [:: E 1; E 2; E 3; E 4] [::] mk_LEA.
Proof.
  rewrite /gen_sem_correct /= /low_sem_aux /= => x disp base scale offset gd m m'.
  rewrite !read_oprd_ireg.
  t_xrbindP => ????? Hbase <- ???? Hoffset <- <- <- <- <- /=. 
  rewrite /x86_lea; case: ifP => // Hscale [<-] [<-]; rewrite /mk_LEA /eval_LEA.
  case: base offset Hbase Hoffset => [base | base] [offset | offset] /= <- <-;
    rewrite /decode_addr //=;do 2 f_equal; rewrite !I64_rw -?(check_scale_of Hscale) //.
  f_equal; apply I64.add_commut.
Qed.

Definition LEA_desc := make_instr_desc LEA_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma TEST_gsc :
  gen_sem_correct [:: TYoprd; TYoprd] Ox86_TEST
     implicit_flags
     [:: E 0; E 1] [::] TEST.
Proof.
  move=> x y gd m m'; rewrite /low_sem_aux /= /eval_TEST.
  by t_xrbindP => ???? -> <- ??? -> <- <- <- [<-] [<-] /=; update_set.
Qed.

Definition TEST_desc := make_instr_desc TEST_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma CMP_gsc :
  gen_sem_correct [:: TYoprd; TYoprd] Ox86_CMP
     implicit_flags
     [:: E 0; E 1] [::] CMP.
Proof.
  move=> x y gd m m'; rewrite /low_sem_aux /= /eval_CMP.
  by t_xrbindP => ???? -> <- ??? -> <- <- <- [<-] [<-] /=; update_set.
Qed.

Definition CMP_desc := make_instr_desc CMP_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma AND_gsc :
  gen_sem_correct [:: TYoprd; TYoprd] Ox86_AND
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] AND.
Proof.
  move=> [] // => [x | x] y gd m m'; rewrite /low_sem_aux /= /eval_AND /=.
  + by t_xrbindP => ????? -> <- <- <- [<-] [<-] /=; update_set.
  by t_xrbindP => ???? -> <- ??? -> <- <- <- [<-] <- /=; update_set.
Qed.

Definition AND_desc := make_instr_desc AND_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma OR_gsc :
  gen_sem_correct [:: TYoprd; TYoprd] Ox86_OR
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] OR.
Proof.
  move=> [] // => [x | x] y gd m m'; rewrite /low_sem_aux /= /eval_OR /=.
  + by t_xrbindP => ????? -> <- <- <- [<-] [<-] /=; update_set.
  by t_xrbindP => ???? -> <- ??? -> <- <- <- [<-] <- /=; update_set.
Qed.

Definition OR_desc := make_instr_desc OR_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma XOR_gsc :
  gen_sem_correct [:: TYoprd; TYoprd] Ox86_XOR
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] XOR.
Proof.
  move=> [] // => [x | x] y gd m m'; rewrite /low_sem_aux /= /eval_XOR /=.
  + by t_xrbindP => ????? -> <- <- <- [<-] [<-] /=; update_set.
  by t_xrbindP => ???? -> <- ??? -> <- <- <- [<-] <- /=; update_set.
Qed.

Definition XOR_desc := make_instr_desc XOR_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma NOT_gsc :
  gen_sem_correct [:: TYoprd] Ox86_NOT
     [:: E 0]
     [:: E 0] [::] NOT.
Proof.
  move=> [] // => [x | x] gd m m'; rewrite /low_sem_aux /= /eval_NOT /=.
  + by move=> [<-].
  by t_xrbindP => ???? -> <- <- [<-] <- /=; update_set.
Qed.

Definition NOT_desc := make_instr_desc NOT_gsc.

(* ----------------------------------------------------------------------------- *)

Lemma SHL_gsc :
  gen_sem_correct [:: TYoprd; TYireg] Ox86_SHL
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] SHL.
Proof.
  move=> [] // => [x | x] y gd m m'; rewrite /low_sem_aux /= /eval_SHL /= /x86_shl /=.
  + t_xrbindP => ???? vy;rewrite read_oprd_ireg => -[->] <- <- <- /=.
    case: ifP => Heq [<-] <-.   
    + rewrite /sets_low /= /mem_write_reg;case:m => ??? /=.
      rewrite -RegMap_set_id; update_set.
Admitted.

Definition SHL_desc := make_instr_desc SHL_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma SHR_gsc :
  gen_sem_correct [:: TYoprd; TYireg] Ox86_SHR
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] SHR.
Proof.
Admitted.

Definition SHR_desc := make_instr_desc SHR_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma SAR_gsc :
  gen_sem_correct [:: TYoprd; TYireg] Ox86_SAR
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] SAR.
Proof.
Admitted.

Definition SAR_desc := make_instr_desc SAR_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma SHLD_gsc :
  gen_sem_correct [:: TYoprd; TYreg; TYireg] Ox86_SHLD
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1; E 2] [::] SHLD.
Proof.
Admitted.

Definition SHLD_desc := make_instr_desc SHLD_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma Set0_gsc : 
  gen_sem_correct [:: TYoprd] Oset0
     (implicit_flags ++ [:: E 0])
     [::] [::] (fun x => XOR x x).
Proof.
  move=> []// => [x|x] gd m m'; rewrite /low_sem_aux /= /eval_XOR /=.
  + move=> [<-]; rewrite I64.xor_idem; update_set.
  rewrite /sets_low /= /decode_addr /=;set addr := I64.add _ _.
  rewrite /mem_write_mem; t_xrbindP => m1 /= Hw <-.
  have : Memory.valid_addr (xmem m) addr.
  + apply /Memory.writeV;eauto.
  move=> /Memory.readV [v ->] /=;rewrite I64.xor_idem Hw /=; update_set.
Qed.

Definition Set0_desc := make_instr_desc Set0_gsc.
  
(* ----------------------------------------------------------------------------- *)

Definition sopn_desc (c : sopn) :=
  match c with
  | Omulu | Oaddcarry | Osubcarry => None
  | Oset0 => Some Set0_desc
  | Ox86_MOV     => Some MOV_desc
  | Ox86_CMOVcc  => Some CMOVcc_desc
  | Ox86_ADD     => Some ADD_desc
  | Ox86_SUB     => Some SUB_desc
  | Ox86_MUL     => Some MUL_desc
  | Ox86_IMUL    => Some IMUL_desc
  | Ox86_IMUL64  => Some IMUL64_desc
  | Ox86_IMUL64imm  => Some IMUL64imm_desc
  | Ox86_DIV     => Some DIV_desc
  | Ox86_IDIV    => Some IDIV_desc
  | Ox86_ADC     => Some ADC_desc
  | Ox86_SBB     => Some SBB_desc
  | Ox86_NEG     => Some NEG_desc
  | Ox86_INC     => Some INC_desc
  | Ox86_DEC     => Some DEC_desc
  | Ox86_SETcc   => Some SETcc_desc
  | Ox86_LEA     => Some LEA_desc
  | Ox86_TEST    => Some TEST_desc
  | Ox86_CMP     => Some CMP_desc
  | Ox86_AND     => Some AND_desc
  | Ox86_OR      => Some OR_desc
  | Ox86_XOR     => Some XOR_desc
  | Ox86_NOT     => Some NOT_desc
  | Ox86_SHL     => Some SHL_desc
  | Ox86_SHR     => Some SHR_desc
  | Ox86_SAR     => Some SAR_desc
  | Ox86_SHLD    => Some SHLD_desc
  end.

Lemma sopn_desc_name o d : sopn_desc o = Some d -> d.(id_name) = o.
Proof. by case: o => //= -[<-]. Qed.

(* -------------------------------------------------------------------- *)
(* High level to mixed semantics                                        *)

Definition check_sopn_arg (loargs : seq pexpr) (x : pexpr) (ad : arg_desc) :=
  match ad with
  | ADImplicit y => is_var y x
  | ADExplicit n o => 
    (n < size loargs) && (x == nth x loargs n) &&
    match o with
    | None => true
    | Some y => is_var y x
    end
  end.

Definition is_lvar (x:var) lv := 
  match lv with
  | Lvar y => x == y
  | _ => false
  end.

Definition check_sopn_res (loargs : seq pexpr) (x : lval) (ad : arg_desc) :=
  match ad with
  | ADImplicit y => is_lvar y x
  | ADExplicit n o => 
    (Some x == (onth loargs n >>= lval_of_pexpr)%O) && (o == None)
  end.

Definition check_sopn_args
  (c : sopn) (outx : seq lval) (inx : seq pexpr) (loargs : seq pexpr) :=
  if sopn_desc c is Some id then
       all2 (check_sopn_res loargs) outx id.(id_out)
    && all2 (check_sopn_arg loargs) inx  id.(id_in )
  else false.

Lemma is_varP x e : is_var x e ->  eq_expr e {| v_var := x; v_info := xH |}.
Proof. by case e => //= v /eqP ->. Qed.
  
Lemma check_sopn_argP (loargs hiargs : seq pexpr) (ads : seq arg_desc) :
     all2 (check_sopn_arg loargs) hiargs ads
  -> exists hiargs', omap (mixed_sem_ad_in loargs) ads = Some hiargs' /\ all2 eq_expr hiargs hiargs'.
Proof.
  elim: hiargs ads => [ | e hiargs Hrec] [ | a ads] //=.
  + by move=> _;exists nil.
  move=> /andP [Hc /Hrec [hiargs' [-> Hall]]] /=.
  rewrite /mixed_sem_ad_in; case: a Hc => //=.
  + by move=> y /is_varP Hy;eexists;split;[by eauto | ];rewrite /= Hy.
  move=> n o /andP [] /andP [] Hlt /eqP -> Ho.
  exists  (nth e loargs n :: hiargs').
  rewrite (onth_nth_size e Hlt) /= Hall andbT;split;last by apply eq_expr_refl.
  by case: o Ho => // y ->.
Qed.

Lemma is_lvarP x e : is_lvar x e ->  eq_lval e {| v_var := x; v_info := xH |}.
Proof. by case e => //= v /eqP ->. Qed.

Lemma check_sopn_resP (loargs : seq pexpr) (lval : seq lval) (ads : seq arg_desc) :
     all2 (check_sopn_res loargs) lval ads
  -> exists lval', omap (mixed_sem_ad_out loargs) ads = Some lval' /\ all2 eq_lval lval lval'.
Proof.
  elim: lval ads => [ | lv lval Hrec] [ | a ads] //=.
  + by move=> _;exists nil.
  move=> /andP [Hc /Hrec [lval' [-> Hall]]] /=.
  rewrite /mixed_sem_ad_out; case: a Hc => //=.
  + by move=> y /is_lvarP Hy;eexists;split;[by eauto | ];rewrite /= Hy.
  move=> n o /andP [] /eqP <- /eqP ->;eexists;split;[by eauto | ].
  by rewrite /= eq_lval_refl.
Qed.

Lemma eq_exprsP gd m es1 es2:
  all2 eq_expr es1 es2 → sem_pexprs gd m es1 = sem_pexprs gd m es2.
Proof.
 rewrite /sem_pexprs.
 by elim: es1 es2 => [ | ?? Hrec] [ | ??] //= /andP [] /eq_exprP -> /Hrec ->.
Qed.

Lemma eq_lvalP gd m lv lv' v : 
  eq_lval lv lv' ->
  write_lval gd lv v m = write_lval gd lv' v m.
Proof.
  case: lv lv'=> [ ?? | [??] | [??] e | [??] e] [ ?? | [??] | [??] e' | [??] e'] //=.
  + by move=> /eqP ->.
  + by move=> /eqP ->.
  + by move=> /andP [/eqP -> /eq_exprP ->].
  by move=> /andP [/eqP -> /eq_exprP ->].
Qed.

Lemma eq_lvalsP gd m ls1 ls2 vs:
  all2 eq_lval ls1 ls2 → write_lvals gd m ls1 vs =  write_lvals gd m ls2 vs.
Proof.
 rewrite /write_lvals.
 elim: ls1 ls2 vs m => [ | l1 ls1 Hrec] [ | l2 ls2] //= [] // v vs m.
 by move=> /andP [] /eq_lvalP -> /Hrec; case: write_lval => /=.
Qed.


Theorem check_sopnP gd o descr outx inx loargs m1 m2 :
     sopn_desc o = Some descr  
  -> check_sopn_args o outx inx loargs
  -> sem_sopn gd o m1 outx inx = ok m2 
  -> mixed_sem gd m1 descr loargs = ok m2.
Proof.
  rewrite /check_sopn_args => Hdesc; rewrite Hdesc => /andP [h1 h2].
  rewrite /mixed_sem /sem_sopn.
  have [inx' [-> /eq_exprsP ->]] := check_sopn_argP h2.
  have [outx' [-> /eq_lvalsP H]]:= check_sopn_resP h1.
  rewrite (sopn_desc_name Hdesc).
  by t_xrbindP => vs ws -> /= ->;rewrite H. 
Qed.

(* ----------------------------------------------------------------------------- *)

Inductive source_position := 
  | InArgs of nat
  | InRes  of nat.

Definition pexpr_of_lval (lv:lval) := 
  match lv with 
  | Lnone _ _ => None 
  | Lvar x    => Some (Pvar x)
  | Lmem x e  => Some (Pload x e)
  | Laset _ _ => None
  end.

Definition get_loarg (outx: seq lval) (inx:seq pexpr) (d:source_position) := 
  match d with
  | InArgs x => onth inx x
  | InRes  x => onth outx x >>= pexpr_of_lval 
  end%O.

(* FIXME: provide a more efficiant version of map on nat here *)
Definition nmap (T:Type) := nat -> option T.
Definition nget (T:Type) (m:nmap T) (n:nat) := m n.
Definition nset (T:Type) (m:nmap T) (n:nat) (t:T) := 
  fun x => if x == n then Some t else nget m x.
Definition nempty (T:Type) := fun n:nat => @None T.

Definition set_expr (m:nmap source_position) (n:nat) (x:source_position) :=
  match nget m n with
  | Some _ => m 
  | None   => nset m n x
  end.

Definition compile_hi_arg (p:nat -> source_position) (ad: arg_desc) (i:nat) (m: nmap source_position) := 
  match ad with
  | ADImplicit _ => m
  | ADExplicit n => set_expr m n (p i)
  end.

Definition mk_loargs (c : cmd_name)  :=
  let: id := get_id c in
  let m := foldl (fun m p => compile_hi_arg InArgs p.1 p.2 m) (nempty _)
                 (zip id.(id_in) (iota 0 (size id.(id_in)))) in
  let m := foldl (fun m p => compile_hi_arg InRes p.1 p.2 m) m
                 (zip id.(id_out) (iota 0 (size id.(id_out)))) in 
  odflt [::] (omap (nget m) (iota 0 (size id.(id_lo)))).

Definition compile_hi_cmd (c : cmd_name) (outx : seq var) (inx : seq expr) := 
  let: id := get_id c in
  omap (get_loarg outx inx) (mk_loargs c) >>= fun loargs =>
    if check_cmd_args c outx inx loargs then Some loargs
    else None.

Lemma compile_hiP (c : cmd_name) (outx : seq var) (inx : seq expr) loargs :
  compile_hi_cmd c outx inx = Some loargs ->
  check_cmd_args c outx inx loargs.
Proof. by move=> /obindI [loargs'] [H1];case:ifP => // ? [<-]. Qed.

Theorem L1 c outx inx m1 m2 loargs :
     compile_hi_cmd c outx inx = Some loargs 
  -> semc m1 (c, outx, inx) = Some m2
  -> sem_id m1 (get_id c) loargs = Some m2.
Proof. by move=> /compile_hiP;apply L0. Qed.

(* -------------------------------------------------------------------- *)
(* Mixed semantics to generated ASM semantics                           *)

Variant lom_eqv (m : mem) (lom : lomem) :=
  | MEqv of
      (forall r, VInt  (lom.(lm_reg) r) = get m (var_of_register r))
    & (forall f, VBool (lom.(lm_fgs) f) = get m (var_of_flag f)).

Definition ireg_of_expr (arg: expr) : option ireg :=
  match arg with
  | EVar x => ssrfun.omap IRReg (register_of_var x)
  | EInt i => Some (IRImm i)
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
  case: (onth_omap_size (EInt 0) hirs hx) => y [hy eqy].
  rewrite hy /= hlo /=.
  eexists; split; first by reflexivity.
  rewrite /=; f_equal => //.
  rewrite eval_lo_arg_of_ireg /=.
  case eqx: nth eqy => [ vx | i ]; last by case => <-.
  case: eqm => eqm _.
  by case eq1: register_of_var => [ z | ] // [] <-; rewrite eqm (var_of_register_of_var eq1).
Qed.

Lemma lom_eqv_set_register m lom x r i :
  lom_eqv m lom →
  register_of_var x = Some r →
  lom_eqv (set m x (VInt i)) (write_reg lom r i).
Proof.
  case => hr hf hx; rewrite -(var_of_register_of_var hx) => {x hx}.
  split => q; rewrite get_set /=.
  + case: eqP; first by move ->; rewrite eq_refl.
    move => ne; case: eqP => // /var_of_register_inj //.
  case: eqP => // h; elim: (var_of_register_var_of_flag (esym h)).
Qed.

Lemma lom_eqv_set_flag m lom x f b :
  lom_eqv m lom →
  flag_of_var x = Some f →
  lom_eqv (set m x (VBool b)) (write_flag lom f b).
Proof.
  case => hr hf hx; rewrite -(var_of_flag_of_var hx) => {x hx}.
  split => q; rewrite get_set /=.
  + case: eqP => // h; elim: (var_of_register_var_of_flag h).
  case: eqP; first by move ->; rewrite eq_refl.
  move => ne; case: eqP => // /var_of_flag_inj //.
Qed.

Lemma set_lom_eqv m lom x y v lom' :
  lom_eqv m lom →
  compile_var x = Some y →
  set_lo y v lom = Some lom' →
  lom_eqv (set m x v) lom'.
Proof.
  case => hr hf.
  rewrite /compile_var.
  case e1: register_of_var => [ r | ].
  + case => <-; case: v => // i [] <-.
    exact: lom_eqv_set_register.
  case e2: flag_of_var => // [ i ] [] <-; case: v => //= b [] <-.
  exact: lom_eqv_set_flag.
Qed.

Lemma sets_lo_cons m d ds v vs :
  sets_lo m (d :: ds) (v :: vs) = set_lo d v m >>= λ m', sets_lo m' ds vs.
Proof.
  rewrite {1} /sets_lo /=.
  case: set_lo; last by case: eqP => // _; exact: foldl_bind_None.
  case: eqP.
  + move/succn_inj => eq_sz /=.
     by move => m' /=; rewrite /sets_lo; case: eqP.
  move => ne_sz /= m'.
  by rewrite /sets_lo; case: eqP => // k; elim: ne_sz; rewrite k.
Qed.

Lemma toto_out ads vs out irs m1 lom1 outv m2 :
  lom_eqv m1 lom1 →
  all wf_implicit ads →
  omap ireg_of_expr vs = Some irs →
  omap (sem_ad_out vs) ads = Some out →
  sets m1 out outv = Some m2 →
  ∃ outx, omap (sem_lo_ad_out irs) ads = Some outx ∧
  ∃ lom2 : lomem, sets_lo lom1 outx outv = Some lom2 ∧ lom_eqv m2 lom2.
Proof.
  move => eqm hwf hirs.
  elim: ads out outv m1 lom1 eqm hwf.
  - move => out outv m1 lom1 eqm _ [] <- /setsI [hsz ->]; exists [::]; split => //.
    by case: outv hsz => // _; exists lom1.
  move => ad ads ih args' outv' m1 lom1 eqm h; rewrite /= in h; case/andP: h => hwf hwf'.
  case/omap_consI => arg [] args [] -> ha has /sets_consI [v] [outv] [? hm2]; subst outv'.
  case: ad ha hwf.
  + move => x /= [] ?; subst arg.
    case hd: compile_var => [ d | ] // _.
    have : ∃ lom', set_lo d v lom1 = Some lom'.
    admit.
    case => lom' hlom'.
    have eqm' := set_lom_eqv eqm hd hlom'.
    case: (ih args outv (set m1 x v) lom' eqm' hwf' has hm2)
      => dst [hdst] [lom2] [hlom2 eqm2].
    exists (d :: dst); split; first by rewrite hdst.
    exists lom2; split; first by rewrite sets_lo_cons hlom' /=. done.

  move => n /=.
  case eq1: onth => [ [] q | ] // [] ? _; subst q.
  move: eq1 => /onthP - /(_ (EInt 0)) /andP [] hsz /eqP harg.
  case: (onth_omap_size (EInt 0) hirs hsz) => y [hy]; rewrite harg.
  case eqy: register_of_var => [ y' | ] // - [] ?; subst y.
  have eqy' : compile_var arg = Some (DReg y') by rewrite /compile_var eqy.
  have : ∃ i, v = VInt i.
  admit.
  case => i ?; subst v.
  have : ∃ lom', set_lo (DReg y') i lom1 = Some lom' by eexists.
  case => lom' hlom'.
  have eqm' := set_lom_eqv eqm eqy' hlom'.
  have := ih _ _ _ _ eqm' hwf' has hm2.
  case => dst [hdst] [lom2] [hlom2 eqm2].
  rewrite hy hdst /=.
  eexists; split; first by reflexivity.
  case: hlom' => ?; subst lom'.
  by exists lom2.
Admitted.

(* -------------------------------------------------------------------- *)
Definition compile_lo (tys: seq arg_ty) (args: seq expr) (op: interp_tys tys) : option low_instr :=
  omap ireg_of_expr args >>= fun iregs =>
    @typed_apply_iregs tys iregs op.


Definition compile_gen (c : cmd_name) (args : seq expr) :=
  let id := get_id c in compile_lo args id.(id_sem).

Theorem L2 c vs m1 m2 loid lom1:
     compile_gen c vs = Some loid
  -> sem_id m1 (get_id c) vs = Some m2
  -> lom_eqv m1 lom1
  -> exists lom2, sem_lo_gen lom1 (get_id c) loid = Some lom2
  /\ lom_eqv m2 lom2.
Proof.
rewrite /compile_gen /sem_id => h.
case E1: (omap _) => [args|//].
case E2: (omap _) => [out|//].
rewrite get_id_ok; set op := (X in sem_cmd X).
rewrite /sem_cmd; case E3: (op _) => [outv|//].
rewrite /sem_lo_gen /sem_lo_gen_aux.
move: h. rewrite /compile_lo. case h: omap => // [irs] hirs.
rewrite (proj2 (id_sem_wf hirs)).
rewrite /sem_lo_cmd.
rewrite get_id_ok -/op.
move => hsets heqm.
have [ inx [ E4 E5 ] ] := toto_in heqm (id_in_wf _) h E1. rewrite E4.
have [ outx [ E6 [ lom2 [ E7 E8 ] ] ] ] := toto_out heqm (id_out_wf _) h E2 hsets.
rewrite E6 E5 E3. eauto.
Qed.

(* -------------------------------------------------------------------- *)
(* From generated ASM semantics to TCB ASM semantics                    *)

Lemma compile_cmd_name c vs loid :
  compile_gen c vs = Some loid →
  cmd_name_of_loid loid = c.
Proof.
  rewrite /compile_gen /compile_lo.
  case: omap => // irs h.
  have := @id_sem_wf (get_id c) irs loid h.
  rewrite get_id_ok.
  by case.
Qed.

Theorem L3 c vs m1 m2 loid lom :
     compile_gen c vs = Some loid
  -> sem_id m1 (get_id c) vs = Some m2
  -> lom_eqv m1 lom
  -> lom_eqv m2 (sem_lo lom loid).
Proof.
  move => hc.
  move/L2: (hc) => h/h{h} h/h{h} [lom'] [].
  rewrite -(compile_cmd_name hc).
  move /obindI : (hc) => [irs [? Hwt]].
  have := (id_gen_sem_wf lom Hwt).  
  by rewrite /sem_lo_gen (compile_cmd_name hc) => -> [<-].
Qed.

(* -------------------------------------------------------------------- *)
(* Putting all together                                                 *)

Definition compile (c : cmd_name) (outx : seq var) (inx:seq expr) := 
  compile_hi_cmd c outx inx >>= compile_gen c.

Theorem L (c : cmd_name) (outx : seq var) (inx : seq expr) loid (m1 m2 : mem) lom :
     compile c outx inx = Some loid 
  -> semc m1 (c, outx, inx) = Some m2
  -> lom_eqv m1 lom
  -> lom_eqv m2 (sem_lo lom loid).
Proof. 
  by move=> /obindI [lexprs []] /L1 H1 /L3 H3 /H1 /H3 H4 /H4.
Qed.
