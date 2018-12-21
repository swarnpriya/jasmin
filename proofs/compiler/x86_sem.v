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


(* -------------------------------------------------------------------- *)
Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import ZArith utils strings low_memory word global oseq.
Import Utf8 Relation_Operators.
Import Memory.
Require Import x86_decl x86_instr_decl.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Variant asm : Type :=
| LABEL of label
  (* Jumps *)
| JMP    of label          (* Unconditional jump *)
| Jcc    of label & condt  (* Conditional jump *)
| AsmOp     of asm_op & asm_args.

(* -------------------------------------------------------------------- *)
Record x86_mem : Type := X86Mem {
  xmem : mem;
  xreg : regmap;
  xxreg: xregmap;
  xrf  : rflagmap;
}.

Record x86_state := X86State {
  xm   :> x86_mem;
  xc   : seq asm;
  xip  : nat;
}.

Notation x86_result := (result error x86_mem).
Notation x86_result_state := (result error x86_state).

(* -------------------------------------------------------------------- *)
Definition eval_cond (c : condt) (rm : rflagmap) :=
  let get rf :=
    if rm rf is Def b then ok b else undef_error in

  match c with
  | O_ct   => get OF
  | NO_ct  => Let b := get OF in ok (~~ b)
  | B_ct   => get CF
  | NB_ct  => Let b := get CF in ok (~~ b)
  | E_ct   => get ZF
  | NE_ct  => Let b := get ZF in ok (~~ b)
  | S_ct   => get SF
  | NS_ct  => Let b := get SF in ok (~~ b)
  | P_ct   => get PF
  | NP_ct  => Let b := get PF in ok (~~ b)

  | BE_ct =>
      Let cf := get CF in
      Let zf := get ZF in ok (cf || zf)

  | NBE_ct =>
      Let cf := get CF in
      Let zf := get ZF in ok (~~ cf && ~~ zf)

  | L_ct =>
      Let sf  := get SF in
      Let of_ := get OF in ok (sf != of_)

  | NL_ct =>
      Let sf  := get SF in
      Let of_ := get OF in ok (sf == of_)

  | LE_ct =>
      Let zf  := get ZF in
      Let sf  := get SF in
      Let of_ := get OF in ok (zf || (sf != of_))

  | NLE_ct =>
      Let zf  := get ZF in
      Let sf  := get SF in
      Let of_ := get OF in ok (~~ zf && (sf == of_))
  end.

(* -------------------------------------------------------------------- *)
Definition st_write_ip (ip : nat) (s : x86_state) :=
  {| xm := s.(xm);
     xc   := s.(xc);
     xip  := ip; |}.

(* -------------------------------------------------------------------- *)
Definition is_label (lbl: label) (i: asm) : bool :=
  match i with
  | LABEL lbl' => lbl == lbl'
  | _ => false
  end.

(* -------------------------------------------------------------------- *)
Definition find_label (lbl : label) (a : seq asm) :=
  let idx := seq.find (is_label lbl) a in
  if idx < size a then ok idx else type_error.

(* -------------------------------------------------------------------- *)
Definition eval_JMP lbl (s: x86_state) : x86_result_state :=
  Let ip := find_label lbl s.(xc) in ok (st_write_ip ip.+1 s).

(* -------------------------------------------------------------------- *)
Definition eval_Jcc lbl ct (s: x86_state) : x86_result_state :=
  Let b := eval_cond ct s.(xrf) in
  if b then eval_JMP lbl s else ok (st_write_ip (xip s).+1 s).

(* -------------------------------------------------------------------- *)
Definition st_get_rflag (rf : rflag) (s : x86_mem) :=
  if s.(xrf) rf is Def b then ok b else undef_error.


(* -------------------------------------------------------------------- *)

Definition decode_addr (s : x86_mem) (a : address) : pointer := nosimpl (
  let: disp   := a.(ad_disp) in
  let: base   := odflt 0%R (Option.map (s.(xreg)) a.(ad_base)) in
  let: scale  := word_of_scale a.(ad_scale) in
  let: offset := odflt 0%R (Option.map (s.(xreg)) a.(ad_offset)) in
  disp + base + scale * offset)%R.

(* -------------------------------------------------------------------- *)

Section GLOB_DEFS.

Context (gd: glob_decls).

Definition check_oreg or ai := 
  match or, ai with
  | Some r, Reg r' => r == r' 
  | Some _, Imm _ _ => true
  | Some _, _      => false
  | None, _        => true
  end.

Definition eval_arg_in_word (s:x86_mem) (args:asm_args) (sz:wsize) (ad:arg_desc) : exec (word sz) := 
  match ad with
  | ADImplicit (IAreg r)   => ok (zero_extend sz (s.(xreg) r))
  | ADImplicit (IArflag f) => type_error
  | ADExplicit i or    =>
    match onth args i with
    | None => type_error
    | Some a =>
      Let _ := assert (check_oreg or a) ErrType in
      match a with
      | Condt _   => type_error 
      | Imm sz' w => ok (zero_extend sz w)
      | Glob g    => Let w := get_global_word  gd g  in ok (zero_extend sz w)
      | Reg r     => ok (zero_extend sz (s.(xreg) r))
      | Adr adr   => read_mem s.(xmem) (decode_addr s adr) sz 
      | XMM x     => ok (zero_extend sz (s.(xxreg) x))
      end
    end
  end.
 
Definition eval_arg_in_bool (s:x86_mem) (args:asm_args) (ad:arg_desc) : exec bool := 
  match ad with
  | ADImplicit (IAreg r)   => type_error 
  | ADImplicit (IArflag f) => Let b := st_get_rflag f s in ok b
  | ADExplicit i or    =>
    match onth args i with
    | None => type_error
    | Some a =>
      Let _ := assert (check_oreg or a) ErrType in
      match a with
      | Condt c => Let b := eval_cond c s.(xrf) in ok b 
      | _       => type_error
      end
    end
  end.

Definition eval_arg_in (s:x86_mem) (args:asm_args) (ty:xtype) (ad:arg_desc) : exec (sem_xt ty) := 
  match ty with
  | xword sz => eval_arg_in_word s args sz ad
  | xbool    => eval_arg_in_bool s args ad
  end.

Fixpoint app_asm_op T (s:x86_mem) (args:asm_args) (tin : seq (arg_desc * xtype)) : 
   sem_xprod (map snd tin) (exec T) -> exec T :=
  match tin return sem_xprod (map snd tin) (exec T) → exec T with
  | [::] => λ (o : exec T),  o 
  | aty :: tin => λ (o : sem_xprod (aty.2:: map snd tin) (exec T)),
    Let v := eval_arg_in s args aty.2 aty.1 in
    @app_asm_op T s args tin (o v)
  end.

(* -------------------------------------------------------------------- *)

Definition o2rflagv (b:option bool) : RflagMap.rflagv := 
  if b is Some b then Def b else Undef.

Definition mem_write_rflag (s : x86_mem) (f:rflag) (b:option bool) :=
  {| xmem  := s.(xmem);
     xreg  := s.(xreg);
     xxreg := s.(xxreg);
     xrf   := RflagMap.oset s.(xrf) f (o2rflagv b);
   |}.

(* -------------------------------------------------------------------- *)
Definition mem_write_mem (l : pointer) sz (w : word sz) (s : x86_mem) :=
  Let m := write_mem s.(xmem) l sz w in ok
  {| xmem := m;
     xreg := s.(xreg);
     xxreg := s.(xxreg);
     xrf  := s.(xrf);
  |}.

(* -------------------------------------------------------------------- *)
Definition mem_write_xreg (r: xmm_register) (w: u256) (m: x86_mem) :=
  {|
    xmem := m.(xmem);
    xreg := m.(xreg);
    xxreg := XRegMap.set m.(xxreg) r w;
    xrf  := m.(xrf);
  |}.

Definition update_u256 (f: msb_flag) (old: u256) (sz: wsize) (new: word sz) : u256 :=
  match f with
  | MSB_CLEAR => zero_extend U256 new
  | MSB_MERGE =>
    let m : u256 := wshl (-1)%R (wsize_bits sz) in
    wxor (wand old m) (zero_extend U256 new)
  end.

Definition mem_update_xreg f (r: xmm_register) sz (w: word sz) (m: x86_mem) : x86_mem :=
  let old := xxreg m r in
  let w' := update_u256 f old w in
  mem_write_xreg r w' m.

(* -------------------------------------------------------------------- *)

Definition word_extend_reg (r: register) sz (w: word sz) (m: x86_mem) := 
  merge_word (m.(xreg) r) w.

Lemma word_extend_reg_id r sz (w: word sz) m :
  (U32 ≤ sz)%CMP →
  word_extend_reg r w m = zero_extend U64 w.
Proof.
rewrite /word_extend_reg /merge_word.
by case: sz w => //= w _; rewrite wand0 wxor0.
Qed.

Definition mem_write_reg (r: register) sz (w: word sz) (m: x86_mem) :=  
  {|
    xmem := m.(xmem);
    xreg := RegMap.set m.(xreg) r (word_extend_reg r w m);
    xxreg := m.(xxreg);
    xrf  := m.(xrf);
  |}.

Definition mem_write_word (f:msb_flag) (s:x86_mem) (args:asm_args) (ad:arg_desc) (sz:wsize) (w: word sz) : exec x86_mem := 
  match ad with
  | ADImplicit (IAreg r)   => ok (mem_write_reg r w s) 
  | ADImplicit (IArflag f) => type_error
  | ADExplicit i or    =>
    match onth args i with
    | None => type_error
    | Some a =>
      Let _ := assert (check_oreg or a) ErrType in
      match a with
      | Reg r     => ok (mem_write_reg r w s) 
      | Adr adr   => mem_write_mem (decode_addr s adr) w s 
      | XMM x     => ok (mem_update_xreg f x w s)
      | _         => type_error
      end
    end
  end.

Definition mem_write_bool(s:x86_mem) (args:asm_args) (ad:arg_desc) (b:option bool) : exec x86_mem := 
  match ad with
  | ADImplicit (IArflag f) => ok (mem_write_rflag s f b)
  | _ => type_error
  end.

Definition mem_write_ty (f:msb_flag) (s:x86_mem) (args:asm_args) (ad:arg_desc) (ty:xtype) : sem_oxt ty -> exec x86_mem := 
  match ty return sem_oxt ty -> exec x86_mem with
   | xword sz => @mem_write_word f s args ad sz
   | xbool    => mem_write_bool s args ad
   end.
   
Fixpoint mem_write_res (f:msb_flag) (args:asm_args) (tout : seq (arg_desc * xtype)) (s:x86_mem) : sem_xtuple (map snd tout) -> exec x86_mem :=
  match tout return sem_xtuple (map snd tout) -> exec x86_mem with
  | [::] => fun _ => ok s
  | aty1 :: tout1 => 
    let rec := @mem_write_res f args tout1 in
    match tout1 return (x86_mem -> sem_xtuple (map snd tout1) -> exec x86_mem) -> (sem_xtuple (map snd (aty1 :: tout1))) -> exec x86_mem with
    | [::] => λ _ (v : sem_oxt aty1.2), @mem_write_ty f s args aty1.1 aty1.2 v
    | aty2 :: tout2 => 
      λ (rec:x86_mem -> sem_xtuple (map snd (aty2::tout2)) -> exec x86_mem)
        (p: sem_oxt aty1.2 * sem_xtuple (map snd (aty2::tout2))),
        Let s := @mem_write_ty f s args aty1.1 aty1.2 p.1 in
        rec s p.2 
    end rec
  end. 

Definition eval_instr_op idesc args (s:x86_mem) : exec x86_mem := 
  Let _   := assert (idesc.(id_check) args) ErrType in
  Let p   := app_asm_op s args idesc.(id_semi) in
  mem_write_res idesc.(id_msb_flag) args s p.

(* -------------------------------------------------------------------- *)

Definition eval_instr (i : asm) (s: x86_state) : exec x86_state :=
  match i with
  | LABEL _      => ok (st_write_ip (xip s).+1 s)
  | JMP   lbl    => eval_JMP lbl s
  | Jcc   lbl ct => eval_Jcc lbl ct s
  | AsmOp o args =>
    let id := instr_desc o in
    Let m := eval_instr_op id args s.(xm) in
    ok {|
        xm := m;
        xc := s.(xc);
        xip := s.(xip).+1
      |}
  end.

(* -------------------------------------------------------------------- *)
Definition fetch_and_eval (s: x86_state) :=
  if oseq.onth s.(xc) s.(xip) is Some i then
    eval_instr i s
  else type_error.

Definition x86sem1 (s1 s2: x86_state) : Prop :=
  fetch_and_eval s1 = ok s2.

Definition x86sem : relation x86_state := clos_refl_trans x86_state x86sem1.

End GLOB_DEFS.

(* -------------------------------------------------------------------- *)
(* TODO A METTRE DANS X86_DECL *)
Record xfundef := XFundef {
 xfd_stk_size : Z;
 xfd_nstk : register;
 xfd_arg  : seq register;
 xfd_body : seq asm;
 xfd_res  : seq register;
}.

Definition xprog : Type :=
  seq (funname * xfundef).

(* TODO: flags may be preserved *)
(* TODO: restore stack pointer of caller? *)
Variant x86sem_fd (P: xprog) (gd: glob_decls) fn st st' : Prop :=
| X86Sem_fd fd mp st2
   `(get_fundef P fn = Some fd)
   `(alloc_stack st.(xmem) fd.(xfd_stk_size) = ok mp)
    (st1 := mem_write_reg fd.(xfd_nstk) (top_stack mp) {| xmem := mp ; xreg := st.(xreg) ; xxreg := st.(xxreg) ; xrf := rflagmap0 |})
    (c := fd.(xfd_body))
    `(x86sem gd {| xm := st1 ; xc := c ; xip := 0 |} {| xm := st2; xc := c; xip := size c |})
    `(st' = {| xmem := free_stack st2.(xmem) fd.(xfd_stk_size) ; xreg := st2.(xreg) ; xxreg := st2.(xxreg) ; xrf := rflagmap0 |})
    .

Definition x86sem_trans gd s2 s1 s3 :
  x86sem gd s1 s2 -> x86sem gd s2 s3 -> x86sem gd s1 s3 :=
  rt_trans _ _ s1 s2 s3.


