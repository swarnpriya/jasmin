Require Import x86_sem linear_sem.
Import Utf8 Relation_Operators.
Import all_ssreflect all_algebra.
Require Import compiler_util oseq expr psem x86_sem linear x86_variables x86_variables_proofs asmgen.
Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Definition assemble_i (i: linstr) : ciexec asm :=
  let '{| li_ii := ii ; li_i := ir |} := i in
  match ir with
  | Lopn ds op es => 
    Let oa := assemble_sopn ii op ds es in
    ok (AsmOp oa.1 oa.2)

  | Lalign  => ciok ALIGN

  | Llabel lbl =>  ciok (LABEL lbl)

  | Lgoto lbl => ciok (JMP lbl)

  | Lcond e l =>
      Let cond := assemble_cond ii e in
      ciok (Jcc l cond)
  end.

(* -------------------------------------------------------------------- *)
Definition assemble_c (lc: lcmd) : ciexec (seq asm) :=
  mapM assemble_i lc.

(* -------------------------------------------------------------------- *)
Variant x86_gen_error_t :=
| X86Error_StackPointerInArguments (* TODO: better error message *)
| X86Error_SaveRSPtoRSP
| X86Error_NonEmptyStackNotSaved.

Definition x86_gen_error k : instr_error :=
  (xH, Cerr_assembler (AsmErr_string
  match k with
  | X86Error_StackPointerInArguments => "Stack pointer is also an argument"
  | X86Error_SaveRSPtoRSP => "Stack pointer cannot be saved to RSP"
  | X86Error_NonEmptyStackNotSaved => "Stack pointer should be saved"
  end)).

(* -------------------------------------------------------------------- *)
Definition assemble_saved_stack (stk_size: Z) (x: stack_alloc.saved_stack) : ciexec (seq asm * seq asm) :=
  match x with
  | stack_alloc.SavedStackNone =>
    Let _ := assert (stk_size =? 0)%Z (x86_gen_error X86Error_NonEmptyStackNotSaved) in
    ok ([::], [::])
  | stack_alloc.SavedStackReg r =>
    Let r := reg_of_var xH r in
    Let _ := assert (RSP != r) (x86_gen_error X86Error_SaveRSPtoRSP) in
    ok (
        [:: AsmOp (MOV Uptr) [:: Reg r; Reg RSP ]
         ; AsmOp (SUB Uptr) [:: Reg RSP; Imm (wrepr U32 stk_size) ]
         ; AsmOp (AND Uptr) [:: Reg RSP; Imm (wrepr U32 (-32)) ]
        ]
        , [:: AsmOp (MOV Uptr) [:: Reg RSP; Reg r ]])
  | stack_alloc.SavedStackStk ofs =>
    let adr := Adr {| ad_disp := wrepr Uptr ofs ; ad_base := Some RSP ; ad_scale := Scale1 ; ad_offset := None |} in
    ok (
        [:: AsmOp (MOV Uptr) [:: Reg RBP; Reg RSP ]
         ; AsmOp (SUB Uptr) [:: Reg RSP; Imm (wrepr U32 stk_size) ]
         ; AsmOp (AND Uptr) [:: Reg RSP; Imm (wrepr U32 (-32)) ]
         ; AsmOp (MOV Uptr) [:: adr; Reg RBP ]
        ],
        [:: AsmOp (MOV Uptr) [:: Reg RSP; adr ]])
  end.

Definition killed_by_stack_code (x: stack_alloc.saved_stack): seq register :=
  match x with
  | stack_alloc.SavedStackNone => [::]
  | stack_alloc.SavedStackReg r => if reg_of_var xH r is Ok r then [:: r; RSP ] else [::]
  | stack_alloc.SavedStackStk _ => [:: RBP; RSP ]
  end.

Lemma assemble_saved_stack_has_no_label stk_size x prologue epilogue lbl :
  assemble_saved_stack stk_size x = ok (prologue, epilogue) →
  ~~ has (x86_sem.is_label lbl) (prologue ++ epilogue).
Proof.
  case: x => /=; t_xrbindP.
  - by move => _ _ <- <-.
  - by move => _ y _ _ _ <- <-.
  by move => z <- <-.
Qed.

Definition valid_stack_code (c: seq asm) : Prop :=
  ∀ lbl, has (x86_sem.is_label lbl) c = false.

Definition assemble_fd (fd: lfundef) :=
  Let body := assemble_c (lfd_body fd) in
  Let arg := reg_of_vars xH (lfd_arg fd) in
  Let res := reg_of_vars xH (lfd_res fd) in
  Let tosave := reg_of_vars xH (map (fun x => VarI x xH) (lfd_extra fd).1) in
  Let stack_code  := assemble_saved_stack (lfd_stk_size fd) (lfd_extra fd).2 in
  let killed_args := filter (λ r, r \in arg) (killed_by_stack_code (lfd_extra fd).2) in
  Let _ := assert (killed_args == [::]) (x86_gen_error (X86Error_StackPointerInArguments)) in
  let code := stack_code.1 ++ body ++ stack_code.2 in
  ciok (XFundef arg code res tosave).


(* -------------------------------------------------------------------- *)
Definition assemble_prog (p: lprog) : cfexec xprog :=
  if reg_of_string p.(lp_stk_id) is Some RSP
  then map_cfprog assemble_fd p.(lp_funcs)
  else Error (Ferr_fun xH (Cerr_assembler (AsmErr_string "Invalid stack pointer"))).

(* -------------------------------------------------------------------- *)
Lemma assemble_i_is_label a b lbl :
  assemble_i a = ok b →
  linear.is_label lbl a = x86_sem.is_label lbl b.
Proof.
rewrite /assemble_i /linear.is_label ; case a =>  ii [] /=.
- move => lvs op es h.
  by move: h;t_xrbindP => ?? <-.
- by move => [<-].
- by move => lbl' [<-].
- by move => lbl' [<-].
by t_xrbindP => ? ? ? _ [<-].
Qed.

Lemma assemble_c_find_is_label c i lbl:
  assemble_c c = ok i →
  find (linear.is_label lbl) c = find (x86_sem.is_label lbl) i.
Proof.
rewrite /assemble_c.
elim: c i.
- by move => i [<-].
move => a c ih i' /=; t_xrbindP => b ok_b i ok_i <- {i'} /=.
by rewrite (ih i ok_i) (assemble_i_is_label lbl ok_b).
Qed.

Lemma assemble_c_find_label c i lbl:
  assemble_c c = ok i →
  linear.find_label lbl c = x86_sem.find_label lbl i.
Proof.
rewrite /assemble_c /linear.find_label /x86_sem.find_label => ok_i.
by rewrite (mapM_size ok_i) (assemble_c_find_is_label lbl ok_i).
Qed.

Lemma assemble_c_find_label_in_context c body pre post lbl pc :
  assemble_c c = ok body →
  linear.find_label lbl c = ok pc →
  valid_stack_code pre →
  x86_sem.find_label lbl (pre ++ body ++ post) = ok (size pre + pc).
Proof.
  move => /assemble_c_find_label - /(_ lbl) ->.
  rewrite /x86_sem.find_label; case: ifP => // /dup [] /ltP hlt; rewrite -has_find => found [] <-{pc} /(_ lbl).
  rewrite !find_cat {}found !size_cat => ->; case: ltP => //.
  rewrite /addn /addn_rec; Psatz.lia.
Qed.

Section STACK_CODE.

Context (prologue epilogue: seq asm)
        (valid_prologue: valid_stack_code prologue).

Variant match_state (ls: lstate) (xs: x86_state) : Prop :=
| MS body of
  (lom_eqv (to_estate ls) (xm xs))
  &
  (assemble_c (lc ls) = ok body)
  &
  (size prologue + lpc ls = xip xs)
  &
  xc xs = prologue ++ body ++ epilogue
.

Lemma assemble_iP gd i j ls ls' xs :
  match_state ls xs →
  assemble_i i = ok j →
  linear_sem.eval_instr gd i ls = ok ls' →
  ∃ xs' : x86_state,
    x86_sem.eval_instr gd j xs = ok xs' ∧
    match_state ls' xs'.
Proof.
rewrite /linear_sem.eval_instr /x86_sem.eval_instr; case => body eqm eqbody eqpc eqc.
case: i => ii [] /=.
- move => lvs op pes; t_xrbindP => -[op' asm_args] hass <- m hsem <-.
  have [s [-> eqm' /=]]:= assemble_sopnP hsem hass eqm.
  (eexists; split; first by reflexivity).
  by econstructor; try eassumption; rewrite ?to_estate_of_estate -?eqpc /=.
- move => [<-] [<-];eexists;split;first by reflexivity.
  by econstructor; try eassumption; rewrite /setpc -eqpc /=.
- move => lbl [<-] [<-]; eexists; split; first by reflexivity.
  econstructor; try eassumption.
  by rewrite /setpc /= -eqpc.
- move => lbl [<-]; t_xrbindP => pc ok_pc <- {ls'}.
  rewrite /eval_JMP eqc (assemble_c_find_label_in_context epilogue eqbody ok_pc valid_prologue) /=.
  eexists; split; first reflexivity.
  by econstructor => /=; try eassumption.
- t_xrbindP => cnd lbl cndt ok_c [<-] b v ok_v ok_b.
  case: eqm => eqm eqr eqx eqf.
  have [v' [ok_v' hvv']] := eval_assemble_cond eqf ok_c ok_v.
  case: v ok_v ok_b hvv' => // [ b' | [] // ] ok_b [?]; subst b'.
  rewrite /eval_Jcc.
  case: b ok_b => ok_b; case: v' ok_v' => // b ok_v' /= ?; subst b;
    (case: (eval_cond _ _) ok_v' => // [ b | [] // ] [->] {b}).
  + t_xrbindP => pc ok_pc <- {ls'} /=.
    rewrite /eval_JMP eqc (assemble_c_find_label_in_context epilogue eqbody ok_pc valid_prologue) /=.
    eexists; split; first reflexivity.
    by econstructor => /=; try eassumption.
  case => <- /=; eexists; split; first by reflexivity.
  econstructor => //=; try eassumption.
  by rewrite -eqpc.
Qed.

Lemma match_state_step gd ls ls' xs :
  match_state ls xs →
  step gd ls = ok ls' →
  ∃ xs',
  fetch_and_eval gd xs = ok xs' ∧
  match_state ls' xs'.
Proof.
move => ms; rewrite /step /find_instr /fetch_and_eval; case: (ms)=> body _ eqc eqip ->.
case ok_i : onth => [ i | // ].
rewrite - eqip onth_cat.
have [j [/(onth_extend epilogue) -> ok_j]] := mapM_onth eqc ok_i.
exact: assemble_iP.
Qed.

Lemma match_state_sem gd ls ls' xs :
  lsem gd ls ls' →
  match_state ls xs →
  ∃ xs',
    x86sem gd xs xs' ∧
    match_state ls' xs'.
Proof.
move => h; elim/lsem_ind: h xs => {ls ls'}.
- move => ls xs h; exists xs; split => //; exact: rt_refl.
move => ls1 ls2 ls3 h1 h ih xs1 m1.
have [xs2 [x m2]] := match_state_step m1 h1.
have [xs3 [y m3]] := ih _ m2.
exists xs3; split => //.
apply: x86sem_trans; last by eauto.
exact: rt_step.
Qed.

End STACK_CODE.

Section PROG.

Context (p: lprog) (p': xprog) (ok_p': assemble_prog p = ok p') (gd: glob_decls).

Definition get_reg_value (st: x86_mem) (r: register) : value :=
  Vword (xreg st r).

Definition get_reg_values st rs : values :=
  map (get_reg_value st) rs.

Lemma write_vars_uincl ii xs vs s1 s2 rs xm1 :
  write_vars xs vs s1 = ok s2 →
  reg_of_vars ii xs = ok rs →
  lom_eqv s1 xm1 →
  List.Forall2 value_uincl vs (get_reg_values xm1 rs) →
  lom_eqv s2 xm1.
Proof.
elim: xs vs s1 s2 rs.
+ by case => // s1 _ _ [<-] [<-].
move => x xs ih /= [] // v vs s1 s3 rs';
  t_xrbindP => s2 ok_s2 ok_s3 r ok_r rs ok_rs <- {rs'} h /List_Forall2_inv_l [v'] [vs'] [/=] /seq_eq_injL [<- {v'} <- {vs'}] [hv rec].
apply: ih; eauto.
move: ok_s2; rewrite /write_var /set_var /=.
have <- /= := var_of_reg_of_var ok_r.
t_xrbindP => vm;apply: on_vuP => // w hw <- <-.
case: h => h1 h2 h3 h4; constructor => //=.
+ move=> r' v'; rewrite /get_var /on_vu /=.
  case: (r =P r') => [<- | hne].
  + rewrite Fv.setP_eq => -[<-] /=.
    have hu1 : value_uincl (Vword (pw_word w)) v.
    + have [sz [w' [-> -> /=]]]:= to_pwordI hw.
      case: Sumbool.sumbool_of_bool => hle //=.
      by apply word_uincl_zero_ext; apply cmp_nle_le; rewrite hle.
    by apply (value_uincl_trans hu1 hv).
  rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply var_of_register_inj.
  by apply h2. 
+ move=> r' v'; rewrite /get_var /on_vu /=.
  by rewrite Fv.setP_neq //; apply h3.
move=> f v'; rewrite /get_var /on_vu /=.
by rewrite Fv.setP_neq //; apply h4.
Qed.

(* TODO: Move this *)
Lemma truncate_val_uincl ty v v' :
  truncate_val ty v = ok v' →
  value_uincl v' v.
Proof.
apply: rbindP => z hz [<-].
case: ty z hz => /=.
- by move => b /to_boolI ->.
- by move => z /of_val_int ->.
- move => n t; case: v => //= [len a | []//].
  by rewrite /WArray.cast /WArray.uincl; case: ZleP => // ? [<-].
move => sz w /of_val_word [sz'] [w'] [hle -> ->].
exact: word_uincl_zero_ext.
Qed.

Lemma get_reg_of_vars_uincl ii xs rs vm vs (rm: regmap) :
  (∀ r v, get_var vm (var_of_register r) = ok v → value_uincl v (Vword (rm r))) →
  reg_of_vars ii xs = ok rs →
  mapM (λ x : var_i, get_var vm x) xs = ok vs →
  List.Forall2 value_uincl vs (map (λ r, Vword (rm r)) rs).
Proof.
move => h; elim: xs rs vs.
+ by move => _ _ [<-] [<-]; constructor.
move => x xs ih rs' vs' /=; t_xrbindP => r ok_r rs ok_rs <- {rs'} v ok_v vs ok_vs <- {vs'} /=.
constructor; last exact: ih.
apply: h. rewrite -ok_v {ok_v}; f_equal; apply: var_of_register_of_var.
case: x ok_r => /= x _; exact: reg_of_var_register_of_var.
Qed.

Lemma rsp_are_you_align rsp sz :
  wand (rsp - sign_extend U64 (wrepr U32 sz)) (wrepr U64 (-32)) = add rsp (- sz).
Proof.
Admitted.

Lemma prologue_execution m s sz to_save prologue body epilogue :
  assemble_saved_stack sz to_save = ok (prologue, epilogue) →
  eqmem m (add (xreg s RSP) (- sz)) (xmem s) →
  exists2 s',
    x86sem gd {| xm := s ; xc := prologue ++ body ++ epilogue ; xip := 0 |} {| xm := s' ; xc := prologue ++ body ++ epilogue ; xip := size prologue |}
    & eqmem m (xreg s' RSP) (xmem s') ∧ ∀ r, r \notin killed_by_stack_code to_save → xreg s' r = xreg s r.
Proof.
  case: to_save => /=; t_xrbindP.
  - move => _ /assertP /Z_eqP -> <- <-{sz prologue epilogue}; rewrite /= add_0 => eqm.
    by exists s; first exact: rt_refl.
  - move => x r ok_r _ /assertP /negbTE rsp_neq_r <- <- {prologue epilogue} /= eqm; rewrite ok_r.
    eexists.
      apply: rt_trans; first exact: rt_step.
      apply: rt_trans; exact: rt_step.
    rewrite /=.
    split.
      by rewrite /mem_write_reg /= !ffunE /= rsp_neq_r /word_extend_reg /= !ffunE /= rsp_neq_r /merge_word /= !wand0 !wxor0 !zero_extend_u
        rsp_are_you_align.
    move => r'; rewrite !inE negb_or => /andP[] /negbTE r'_neq_r /negbTE r'_neq_RSP.
    by rewrite /mem_write_reg /= !ffunE /= rsp_neq_r /word_extend_reg /= !ffunE /= r'_neq_RSP r'_neq_r.
  move => ofs <- <- {prologue epilogue} eqm.
  have : ∃ m', @write_mem low_mem LM (xmem s) (wrepr U64 ofs + add (xreg s RSP) (- sz)) U64 (xreg s RSP) = ok m'.
  + apply/(@writeV _ _ _ _ LMS).
    admit.
  case => m' ok_m'.
  eexists.
    apply: rt_trans; first exact: rt_step.
    apply: rt_trans; first exact: rt_step.
    apply: rt_trans; apply: rt_step => //=.
    rewrite /x86sem1 /fetch_and_eval /=.
    rewrite /eval_op /=.
    rewrite /exec_instr_op /=.
    rewrite /mem_write_vals /=.
    rewrite /mem_write_val /=.
    rewrite /mem_write_reg /= !ffunE /= /word_extend_reg /= !ffunE /= /decode_addr /= !ffunE /=.
    rewrite /merge_word /= !wand0 !wxor0 !zero_extend_u.
    rewrite /mem_write_mem /=.
    rewrite rsp_are_you_align GRing.mulr0 GRing.addr0.
    rewrite ok_m' /=.
    done.
  split.
  + rewrite /= !ffunE /=.
    admit.
  by move => r; rewrite !inE negb_or => /andP[] /negbTE r_neq_RBP /negbTE r_neq_RSP; rewrite !ffunE r_neq_RSP r_neq_RBP.
Admitted.

(* TODO: this is a general property of fold *)
Lemma write_vars_emem vars vs s s' :
  write_vars vars vs s = ok s' →
  emem s' = emem s.
Proof.
  elim: vars vs s.
  + by case => //= s [] ->.
  by move => x xs ih [] //= v vs s; rewrite /write_var; t_xrbindP => _ ? _ <- /ih{ih} ->.
Qed.

Lemma assemble_fdP m1 fn va m2 vr :
  lsem_fd p gd m1 fn va m2 vr →
  ∃ fd va',
    get_fundef p.(lp_funcs) fn = Some fd ∧
    mapM2 ErrType truncate_val (lfd_tyin fd) va = ok va' ∧
  ∃ fd', get_fundef p' fn = Some fd' ∧
    ∀ st1,
      List.Forall2 value_uincl va' (get_reg_values st1 fd'.(xfd_arg)) →
      eqmem m1 (xreg st1 RSP) st1.(xmem) →
      ∃ st2,
        x86sem_fd p' gd fn st1 st2 ∧
        List.Forall2 value_uincl vr (get_reg_values st2 fd'.(xfd_res)) ∧
        eqmem m2 (xreg st2 RSP) st2.(xmem).
Proof.
case => m1' fd va' vm2 m2' s1 s2 vr' ok_fd ok_m1' /= [<-] {s1} ok_va'.
set vm1 := (vm in {| evm := vm |}).
move => ok_s2 hexec ok_vr' ok_vr -> {m2}.
exists fd, va'. split; first exact: ok_fd. split; first exact: ok_va'.
move: ok_p'; rewrite /assemble_prog.
case ok_sp: (reg_of_string _) => [ [] // | // ] ok_p''.
have [fd' [h ok_fd']] := get_map_cfprog ok_p'' ok_fd.
exists fd'. split; first exact: ok_fd'.
move => s1 hargs eqm1.
move: h; rewrite /assemble_fd; t_xrbindP => body ok_body
 args ok_args dsts ok_dsts tosave ok_tosave [prologue epilogue] ok_stack_code _ /assertP /eqP hsp [?]; subst fd' => /=.
set xr1 := {| xmem := s1.(xmem) ; xreg := s1.(xreg) ; xxreg := s1.(xxreg) ; xrf := rflagmap0 |}.
have ok_prologue : valid_stack_code prologue.
+ move => lbl. have := assemble_saved_stack_has_no_label lbl ok_stack_code.
  by rewrite has_cat negb_or => /andP[] /negbTE.
have :
  exists2 xr2,
    x86sem gd
           {| xm := xr1 ; xc := prologue ++ body ++ epilogue ; xip := 0 |}
           {| xm := xr2 ; xc := prologue ++ body ++ epilogue ; xip := size prologue |}
    & lom_eqv s2 xr2.
+ have ok_xreg : ∀ xr r v, get_var vm1 (var_of_xmm_register r) = ok v → value_uincl v (Vword (xr r)).
  + by move => xr r v; rewrite /get_var Fv.setP_neq // Fv.get0.
  have ok_freg : ∀ m rf, eqflags {| emem := m ; evm := vm1 |} rf.
  + by move => m rf f v; rewrite /get_var Fv.setP_neq // Fv.get0.
  have eqm1' := eqmem_alloc L eqm1 ok_m1'.
  change (xreg s1) with (xreg xr1) in eqm1'.
  change (xmem s1) with (xmem xr1) in eqm1'.
  have [xr2 exec_prologue [ok_mem ok_reg]] := prologue_execution body ok_stack_code eqm1'.
  exists xr2; first exact: exec_prologue.
  apply: (write_vars_uincl ok_s2 ok_args).
  split.
  + exact: ok_mem.
  + rewrite /vm1 /= => r v.
    rewrite (inj_reg_of_string ok_sp (reg_of_stringK RSP)).
    rewrite /get_var /var_of_register /=.
    case: (r =P RSP).
    * move => -> {r} /=; rewrite Fv.setP_eq => -[<-].
      admit.
    move => ne; rewrite /= Fv.setP_neq /vmap0 ?Fv.get0 //.
    by apply/eqP => -[] /(@inj_string_of_register RSP) ?; apply: ne.
  + exact: ok_xreg.
  + exact: ok_freg.
  + replace (get_reg_values xr2 args) with (get_reg_values s1 args); first exact: hargs.
    apply: map_ext => r /xseq.InP hr.
    rewrite /get_reg_value ok_reg; first reflexivity.
    apply/negP => r_killed.
    suff : r \in [::] by [].
    by rewrite -hsp mem_filter hr.
case => xr2 exec_prologue eqm2.
have ms : match_state prologue epilogue (of_estate s2 fd.(lfd_body) 0) {| xm := xr2 ; xc := prologue ++ body ++ epilogue ; xip := size prologue |}.
+ econstructor => //=; first by rewrite to_estate_of_estate. eassumption.
have [[[om or oxr orf] oc opc] [xexec]] := match_state_sem ok_prologue hexec ms.
case => /= body' eqm2'; rewrite ok_body => - [] ???; subst body' opc oc.
have :
  exists2 xr3,
  x86sem gd {|
           xm := {| xmem := om; xreg := or; xxreg := oxr; xrf := orf |};
           xc := prologue ++ body ++ epilogue;
           xip := size prologue + size (lfd_body fd) |}
         {| xm := xr3 ; xc := prologue ++ body ++ epilogue ; xip := size (prologue ++ body ++ epilogue) |}
  & lom_eqv {| emem := free_stack m2' (lfd_stk_size fd) ; evm := vm2 |} xr3.
+ admit.
case => xr3 exec_epilogue eqm3.
eexists; split.
+ econstructor. eassumption. 2: reflexivity.
  apply: x86sem_trans; first exact: exec_prologue.
  apply: x86sem_trans; last exact: exec_epilogue.
  exact: xexec.
case: eqm3 => /= eqm3 eqr _ _.
split; last assumption.
rewrite /get_reg_values /get_reg_value /=.
apply: (Forall2_trans value_uincl_trans).
+ apply: (mapM2_Forall2 _ ok_vr) => a b r _; exact: truncate_val_uincl.
apply: get_reg_of_vars_uincl; eassumption.
(*
*)
Admitted. (*
set xr1 := mem_write_reg sp (top_stack m1') {| xmem := m1' ; xreg := s1.(xreg) ; xxreg := s1.(xxreg) ; xrf := rflagmap0 |}.
have eqm1 : lom_eqv {| emem := m1' ; evm := vm1 |} xr1.
+ constructor => //.
  - rewrite /vm1 /= => r v.
    rewrite (inj_reg_of_string ok_sp (reg_of_stringK sp)).
    rewrite /get_var /var_of_register /RegMap.set ffunE; case: eqP.
    * move => -> {r} /=; rewrite Fv.setP_eq word_extend_reg_id // zero_extend_u => -[<-];
      exact: word_uincl_refl.
    move => ne; rewrite /= Fv.setP_neq /vmap0 ?Fv.get0 //.
    by apply/eqP => -[] /inj_string_of_register ?; apply: ne.
have eqm2 : lom_eqv s2 xr1.
+ by apply: write_vars_uincl; eauto.
have ms : match_state (of_estate s2 fd.(lfd_body) 0) {| xm := xr1 ; xc := body ; xip := 0 |}.
+ by constructor => //=; rewrite to_estate_of_estate.
have [[[om or oxr orf] oc opc] [xexec]] := match_state_sem hexec ms.
rewrite (mapM_size ok_body).
case => eqm' /=.
rewrite ok_body => -[?] ?; subst oc opc.
eexists; split; first by econstructor; eauto.
case: eqm' => /= ?; subst om => eqr' _; split => //.
rewrite /get_reg_values /get_reg_value /=.
apply: (Forall2_trans value_uincl_trans).
+ apply: (mapM2_Forall2 _ ok_vr) => a b r _; exact: truncate_val_uincl.
apply: get_reg_of_vars_uincl; eassumption.
Qed.
*)

End PROG.
