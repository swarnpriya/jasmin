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
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import xseq expr linear sem compiler_util.
(* ------- *) Require Import low_memory x86_sem gen_map memory.

Import Ascii.
Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
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

(* -------------------------------------------------------------------- *)
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
Record xfundef := XFundef {
 xfd_stk_size : Z;
 xfd_nstk : register;
 xfd_arg  : seq register;
 xfd_body : seq asm;
 xfd_res  : seq register;
}.

Definition xprog := seq (funname * xfundef).

(* ** Instruction description * 
 * -------------------------------------------------------------------- *)

Variant desc_kind := 
  | Flag of rflag
  | Reg  of register
  | Ireg of option register 
  | Addr
  | Oprd 
  | Condt. 

Variant oprd_t  := 
  | Toprd 
  | Tcondt.

Variant oprd_kind := 
  | FLAG  of rflag
  | REG   of register
  | IREG  of ireg
  | ADDR  of address 
  | OPRD  of oprd
  | CONDT of condt.

Parameter oprd_kind_beq : oprd_kind -> oprd_kind -> bool.

Lemma oprd_kind_eq_axiom : Equality.axiom oprd_kind_beq.
Proof.
Admitted.

Definition oprd_kind_eqMixin := Equality.Mixin oprd_kind_eq_axiom.
Canonical oprd_kind_eqType := EqType oprd_kind oprd_kind_eqMixin.
 
Definition arg_desc := seq (desc_kind * option positive).

Definition interp_t (t:oprd_t) := 
  match t with
  | Toprd => oprd
  | Tcondt => condt
  end.

Fixpoint interp_instr (ts:seq oprd_t) :=
  match ts with
  | [::] => asm
  | t :: ts => interp_t t -> interp_instr ts 
  end.

Record instr_desc := MkID {
  dest_desc  : arg_desc;
  src_desc   : arg_desc;
  nargs_desc : nat;
}.

Definition oprd_map := Mp.t oprd_kind.

Definition x86_instr_desc : Type := sopn * Mp.t oprd_kind.

Definition write_oprd_kind (o : oprd_kind) (v : value) (s : x86_state) :=
  match o with
  | OPRD o          => Let w := to_word v in write_oprd o w s
  | REG  r          => Let w := to_word v in ok (st_write_reg r w s)
  | ADDR a          => Let w := to_word v in st_write_mem (decode_addr s a) w s
  | IREG (Imm_ir _) => type_error
  | IREG (Reg_ir r) => Let w := to_word v in ok (st_write_reg r w s)
  | FLAG r          => Let b := to_bool v in ok (st_set_rflags r b s)
  | CONDT _         => type_error
  end.

(* -------------------------------------------------------------------- *)
Definition to_rbool (v : value) :=
  match v with
  | Vbool   b    => ok (Def b)
  | Vundef sbool => ok Undef
  | _            => type_error
  end.

(* -------------------------------------------------------------------- *)
Definition of_rbool (v : RflagMap.rflagv) :=
  if v is Def b then Vbool b else Vundef sbool.

Definition read_oprd_kind gd (o : oprd_kind) (s : x86_state) :=
  match o return result _ value with
  | OPRD o =>
      Let w := read_oprd gd o s in ok (Vword w)

  | IREG (Reg_ir r)
  | REG r =>
      ok (Vword (s.(xreg) r))

  | ADDR a =>
      Let w := Memory.read_mem s.(xmem) (decode_addr s a) in ok (Vword w)

  | IREG (Imm_ir i) =>
      ok (Vword i)

  | FLAG r =>
      ok (of_rbool (s.(xrf) r))

  | _ => type_error
  end.

Definition eval_read
  (gd : glob_defs) (adesc : desc_kind * option positive)
  (args : Mp.t oprd_kind) (s : x86_state)
:=
  match adesc with
  | (Flag rf, None  ) => rmap Vbool (st_get_rflag rf s)
  | (Reg  rg, None  ) => ok (Vword (s.(xreg) rg))
  | (Addr   , Some i)
  | (Oprd   , Some i) =>
      Let op := o2r ErrType (Mp.get args i) in
      read_oprd_kind gd op s
  | (_      , _     ) => Error ErrType
  end.

Definition eval_write
  (adesc : desc_kind * option positive) (args : Mp.t oprd_kind)
  (v : value) (s0 s : x86_state)
:=
  match adesc with
  | (Flag rf, None) =>
      Let b := to_bool v in ok (st_set_rflags rf b s)

  | (Reg rg, None) =>
      Let w := to_word v in ok (st_write_reg rg w s)

  | (Oprd, Some i)
  | (Addr, Some i) =>
      Let op := o2r ErrType (Mp.get args i) in
      write_oprd_kind op v s

  | (_, _) => Error ErrType
  end.

Definition eval_instr
  (g : glob_defs) (xid : x86_instr_desc) (id : instr_desc) (s : x86_state)
:=
  Let args := mapM (fun src => eval_read g src xid.2 s) id.(src_desc) in
  Let out  := sem_sopn xid.1 args in

  fold2 ErrType
    (fun desc v s' => eval_write desc xid.2 v s s')
    id.(dest_desc) out s.

(* instr_desc : instruction description (args, output, #  args) *)
(* oprd : operator argument *)
(* oprd_kind : operator argument value *)

Definition eval_instr_seq
  (g : glob_defs) (xid : sopn * seq oprd_kind) (id : instr_desc) (s : x86_state)
:=
  let: (_, args) :=
    foldl (fun im x => ((im.1+1)%positive, Mp.set im.2 im.1 x))
          (1%positive, Mp.empty _) xid.2
  in eval_instr g (xid.1, args) id s.

(* MOV *)
Definition mov_desc := 
  {| dest_desc  := [:: (Oprd, Some 1%positive)];
     src_desc   := [:: (Oprd, Some 2%positive)];
     nargs_desc := 2; |}.

(* ADC *)
Definition adc_desc := 
  {| dest_desc := [:: (Flag OF, None);
                      (Flag CF, None);
                      (Flag SF, None);
                      (Flag PF, None);
                      (Flag ZF, None); 
                      (Oprd, Some 1%positive) ];
     src_desc  := [:: (Oprd, Some 1%positive);
                      (Oprd, Some 2%positive);
                      (Flag CF, None) ];
     nargs_desc := 2; |}.

Definition set_oprd (m:oprd_map) o k := 
  oapp (fun p => Mp.set m p k) m o.

(* ** Conversion to assembly *
 * -------------------------------------------------------------------- *)

Definition invalid_rflag (s: string) : asm_error :=
  AsmErr_string ("Invalid rflag name: " ++ s).

Definition invalid_register (s: string) : asm_error :=
  AsmErr_string ("Invalid register name: " ++ s).

Global Opaque invalid_rflag invalid_register.

(* -------------------------------------------------------------------- *)

Definition asm_error {A} ii s := 
  @cierror ii (Cerr_assembler (AsmErr_string s)) A.

Definition rflag_of_var ii (v: var) :=
  match v with
  | Var sbool s =>
     match (rflag_of_string s) with
     | Some r => ciok r
     | None => cierror ii (Cerr_assembler (invalid_rflag s))
     end
  | _ => asm_error ii "Invalid rflag type"
  end.

(* -------------------------------------------------------------------- *)
Definition reg_of_var ii (v: var) :=
  match v with
  | Var sword s =>
     match (reg_of_string s) with
     | Some r => ciok r
     | None => cierror ii (Cerr_assembler (invalid_register s))
     end
  | _ =>  asm_error ii "Invalid register type"
  end.
  
Definition rflag_of_lval ii f l :=
  match l with
  | Lvar x    => 
    Let f' := rflag_of_var ii x in
    if f == f' then ok (FLAG f)
    else 
      asm_error ii
        ("Invalid lval: found " ++ string_of_rflag f' ++ 
         " instead of " ++ string_of_rflag f)
  | _ => asm_error ii "Invalid lval: flag expected"
  end.

Definition reg_of_lval ii r l :=
  match l with
  | Lvar x    => 
    Let r' := reg_of_var ii x in
    if r == r' then ok (REG r')
    else 
      asm_error ii
        ("Invalid lval: found " ++ string_of_register r' ++ 
         " instead of " ++ string_of_register r)
  | _ => asm_error ii "Invalid lval: register expected"
  end.

(* -------------------------------------------------------------------- *)
Definition scale_of_z ii z :=
  match z with
  | 1 => ok Scale1
  | 2 => ok Scale2
  | 4 => ok Scale4
  | 8 => ok Scale8
  | _ => asm_error ii "invalid scale"
  end%Z.

Variant ofs := 
  | Ofs_const of Z
  | Ofs_var   of var_i
  | Ofs_mul   of Z & var_i
  | Ofs_add   of Z & var_i & Z
  | Ofs_error.
  
(* -------------------------------------------------------------------- *)
Fixpoint addr_ofs e := 
  match e with
  | Pcast (Pconst z) => Ofs_const z
  | Pvar  x          => Ofs_var x
  | Papp2 (Omul Op_w) e1 e2 =>
    match addr_ofs e1, addr_ofs e2 with
    | Ofs_const n1, Ofs_const n2 => Ofs_const (n1 * n2)%Z
    | Ofs_const sc, Ofs_var   x  => Ofs_mul sc x 
    | Ofs_var   x , Ofs_const sc => Ofs_mul sc x      
    | _           , _            => Ofs_error
    end
  | Papp2 (Oadd Op_w) e1 e2 =>
    match addr_ofs e1, addr_ofs e2 with
    | Ofs_const n1, Ofs_const n2 => Ofs_const (n1 + n2)%Z
    | Ofs_const n , Ofs_var   x  => Ofs_add 1%Z x n
    | Ofs_var   x , Ofs_const n  => Ofs_add 1%Z x n
    | Ofs_mul sc x, Ofs_const n  => Ofs_add sc  x n
    | Ofs_const n , Ofs_mul sc x => Ofs_add sc  x n
    | _           , _            => Ofs_error
    end
  | _ => Ofs_error
  end.

(* -------------------------------------------------------------------- *)
Definition word_of_int (z: Z) := ciok (I64.repr z).

(* -------------------------------------------------------------------- *)
Definition addr_of_pexpr ii s (e: pexpr) :=
  match addr_ofs e with
  | Ofs_const z => 
    Let n := word_of_int z in
    ciok (mkAddress n (Some s) Scale1 None)
  | Ofs_var x =>
    Let x := reg_of_var ii x in
    ciok (mkAddress I64.zero (Some s) Scale1 (Some x))
  | Ofs_mul sc x =>
    Let x := reg_of_var ii x in
    Let sc := scale_of_z ii sc in
    ciok (mkAddress I64.zero (Some s) sc (Some x))
  | Ofs_add sc x z =>
    Let x := reg_of_var ii x in
    Let n := word_of_int z in
    Let sc := scale_of_z ii sc in
    ciok (mkAddress n (Some s) sc (Some x))
  | Ofs_error =>
    asm_error ii "Invalid address expression"
  end.

(* -------------------------------------------------------------------- *)
Definition oprd_of_pexpr ii (e: pexpr) :=
  match e with
  | Pcast (Pconst z) =>
     Let w := word_of_int z in
     ciok (Imm_op w)
  | Pvar v =>
     Let s := reg_of_var ii v in
     ciok (Reg_op s)
  | Pglobal g =>
    ciok (Glo_op g)
  | Pload v e => 
     Let s := reg_of_var ii v in
     Let w := addr_of_pexpr ii s e in
     ciok (Adr_op w)
  | _ => asm_error ii "Invalid pexpr for oprd"
  end.

Definition addr_of_lval ii l :=
  match l with
  | Lmem v e => 
    Let s := reg_of_var ii v in
    Let a := addr_of_pexpr ii s e in
    ciok (ADDR a)
  | _ => asm_error ii "Invalid lval: address expected"
  end.

(* -------------------------------------------------------------------- *)
Definition oprd_of_lval ii (l: lval) :=
  match l with
  | Lnone _ _ => asm_error ii "Lnone found in lval, please report"
  | Lvar v =>
     Let s := reg_of_var ii v in
     ciok (Reg_op s)
  | Lmem v e =>
     Let s := reg_of_var ii v in
     Let a := addr_of_pexpr ii s e in
     ciok (Adr_op a)
  | Laset v e =>  asm_error ii "Laset not handled in assembler, please report "
  end.

Definition match_lval ii (m:oprd_map) (dko: desc_kind * option positive) (l:lval) := 
  Let k := 
    match dko.1 with
    | Flag f => rflag_of_lval ii f l
    | Reg  r => reg_of_lval ii r l 
    | Ireg r => asm_error ii "can not have ireg as a lval"
    | Addr   => addr_of_lval ii l
    | Oprd   => Let oprd := oprd_of_lval ii l in ciok (OPRD oprd)
    | Condt  => asm_error ii "can not have condt as a lval"
    end in
  ok (set_oprd m dko.2 k).

Fixpoint match_lvals ii (m:oprd_map) (ds:arg_desc) (ls:lvals) := 
  match ds, ls with
  | [::], [::] => ok m
  | d::ds, l::ls => 
    Let m := match_lval ii m d l in
    match_lvals ii m ds ls
  | _, _ => asm_error ii "wrong number of lval"
  end.

Definition rflag_of_expr ii f e :=
  match e with
  | Pvar x    => 
    Let f' := rflag_of_var ii x in
    if f == f' then ok (FLAG f)
    else 
      asm_error ii
        ("Invalid expression: found " ++ string_of_rflag f' ++ 
         " instead of " ++ string_of_rflag f)
  | _ => asm_error ii "Invalid expression: flag expected"
  end.

Definition reg_of_expr ii r e :=
  match e with
  | Pvar x    => 
    Let r' := reg_of_var ii x in
    if r == r' then ok (REG r')
    else 
      asm_error ii
        ("Invalid lval: found " ++ string_of_register r' ++ 
         " instead of " ++ string_of_register r)
  | _ => asm_error ii "Invalid lval: register expected"
  end.

(* -------------------------------------------------------------------- *)
Definition assemble_cond ii (e: pexpr) : ciexec condt :=
  match e with
  | Pvar v =>
    Let r := rflag_of_var ii v in
    match r with
    | OF => ok O_ct
    | CF => ok B_ct
    | ZF => ok E_ct
    | SF => ok S_ct
    | PF => ok P_ct
    | DF => asm_error ii "Cannot branch on DF"
    end

  | Papp1 Onot (Pvar v) =>
    Let r := rflag_of_var ii v in
    match r with
    | OF => ok NO_ct
    | CF => ok NB_ct
    | ZF => ok NE_ct
    | SF => ok NS_ct
    | PF => ok NP_ct
    | DF => asm_error ii "Cannot branch on ~~ DF"
    end

  | Papp2 Oor (Pvar vcf) (Pvar vzf) =>
    Let rcf := rflag_of_var ii vcf in
    Let rzf := rflag_of_var ii vzf in
    if ((rcf == CF) && (rzf == ZF)) then
      ok BE_ct
    else asm_error ii "Invalid condition (BE)"

  | Papp2 Oand (Papp1 Onot (Pvar vcf)) (Papp1 Onot (Pvar vzf)) =>
    Let rcf := rflag_of_var ii vcf in
    Let rzf := rflag_of_var ii vzf in
    if ((rcf == CF) && (rzf == ZF)) then
      ok NBE_ct
    else asm_error ii "Invalid condition (NBE)"

  | Pif (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2) =>
    Let rsf := rflag_of_var ii vsf in
    Let rof1 := rflag_of_var ii vof1 in
    Let rof2 := rflag_of_var ii vof2 in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok L_ct
    else asm_error ii "Invalid condition (L)"

  | Pif (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2)) =>
    Let rsf := rflag_of_var ii vsf in
    Let rof1 := rflag_of_var ii vof1 in
    Let rof2 := rflag_of_var ii vof2 in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NL_ct
    else asm_error ii "Invalid condition (NL)"

  | Papp2 Oor (Pvar vzf)
          (Pif (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2)) =>
    Let rzf := rflag_of_var ii vzf in
    Let rsf := rflag_of_var ii vsf in
    Let rof1 := rflag_of_var ii vof1 in
    Let rof2 := rflag_of_var ii vof2 in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok LE_ct
    else asm_error ii "Invalid condition (LE)"

  | Papp2 Oand
             (Papp1 Onot (Pvar vzf))
             (Pif (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2))) =>
    Let rzf := rflag_of_var ii vzf in
    Let rsf := rflag_of_var ii vsf in
    Let rof1 := rflag_of_var ii vof1 in
    Let rof2 := rflag_of_var ii vof2 in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NLE_ct
    else asm_error ii "Invalid condition (NLE)"

  | _ => cierror ii (Cerr_assembler (AsmErr_cond e))
  end.

Definition match_arg ii (m:oprd_map) (dko: desc_kind * option positive) (e:pexpr) := 
  Let k := 
    match dko.1 with
    | Flag f => rflag_of_expr ii f e 
    | Reg  r => reg_of_expr ii r e
    | Ireg r => asm_error ii "can not have ireg as an expression: FIXME"
    | Addr   => asm_error ii "can not have addr as an expression: FIXME"
    | Oprd   => 
      Let oprd := oprd_of_pexpr ii e in
      ciok (OPRD oprd)
    | Condt  => 
      Let condt := assemble_cond ii e in
      ciok (CONDT condt)
    end in
  ok (set_oprd m dko.2 k).

Fixpoint match_args ii (m:oprd_map) (ds:arg_desc) (es:pexprs) := 
  match ds, es with
  | [::], [::] => ok m
  | d::ds, e::es => 
    Let m := match_arg ii m d e in
    match_args ii m ds es
  | _, _ => asm_error ii "wrong number of arguments"
  end.

Definition get_oprd ii (o:oprd_kind) := 
  match o with
  | OPRD o => ok o
  | _      => asm_error ii "invalid instruction descriptor: not an oprd"
  end.

Definition get_condt ii (o:oprd_kind) := 
  match o with
  | CONDT o => ok o
  | _      => asm_error ii "invalid instruction descriptor: not an condt"
  end.

Fixpoint app_map ii (m:oprd_map) (p:positive) (ts: seq oprd_t) (mk: interp_instr ts) := 
  match ts return interp_instr ts -> ciexec asm with
  | [::] => fun i => ok i
  | t :: ts => fun mk =>
    match Mp.get m p with
    | Some arg =>
      Let arg := 
        match t return ciexec (interp_t t) with
        | Toprd  => get_oprd  ii arg
        | Tcondt => get_condt ii arg
        end in
      @app_map ii m (p+1) ts (mk arg)
        
    | None => asm_error ii "invalid instruction descriptor"
    end
  end mk.

Definition desc_opn ii o := 
  match o with
  | Ox86_MOV => ok mov_desc 
  | Ox86_ADC => ok adc_desc
  | _        => asm_error ii "no instruction descriptor"
  end.

Definition assemble_opn_r ii ls d es := 
  Let m := match_args ii (Mp.empty _) d.(dest_desc) es in
  Let m := match_lvals ii m d.(src_desc) ls in
  mapM
   (fun i =>
      let err := (ii, Cerr_assembler (AsmErr_string "")) in
      o2r err (Mp.get m (Pos.of_nat i.+1)))
   (iota 0 d.(nargs_desc)).

Definition assemble_opn ii ls o es := 
  Let d := desc_opn ii o in
  Let a := assemble_opn_r ii ls d es in
  ciok (o, a).

(*
Definition assemble_i (li: linstr) : ciexec asm :=
  let (ii, i) := li in
  match i with
  | Lassgn l _ e =>
     Let dst := oprd_of_lval ii l in
     Let src := oprd_of_pexpr ii e in
     ciok (MOV dst src)

  | Lopn l o p =>
     assemble_opn ii l o p

  | Llabel l =>
      ciok (LABEL l)

  | Lgoto l =>
      ciok (JMP l)

  | Lcond e l =>
      Let cond := assemble_cond ii e in
      ciok (Jcc l cond)
  end.
*)