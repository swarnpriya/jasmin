Require Import x86_instr linear_sem.
Import Utf8.
Import all_ssreflect.
Import compiler_util expr x86_sem linear x86_variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Definition word_of_int (z: Z) := ciok (I64.repr z).

(* -------------------------------------------------------------------- *)
Definition word_of_pexpr ii e :=
  match e with
  | Pcast (Pconst z) => word_of_int z
  | _ => cierror ii (Cerr_assembler (AsmErr_string "Invalid integer constant"))
  end.

(* -------------------------------------------------------------------- *)
Definition oprd_of_lval ii (l: lval) :=
  match l with
  | Lnone _ _ =>
     cierror ii (Cerr_assembler (AsmErr_string "Lnone not implemented"))
  | Lvar v =>
     Let s := reg_of_var ii v in
     ciok (Reg_op s)
  | Lmem v e =>
     Let s := reg_of_var ii v in
     Let w := word_of_pexpr ii e in
     ciok (Adr_op (mkAddress w (Some s) Scale1 None))
  | Laset v e =>
     cierror ii (Cerr_assembler (AsmErr_string "Laset not handled in assembler"))
  end.

(* -------------------------------------------------------------------- *)
Definition assemble_i (i: linstr) : ciexec asm :=
  let '{| li_ii := ii ; li_i := ir |} := i in
  match ir with
  | Lassgn d _ e =>
     Let dst := oprd_of_lval ii d in
     Let src := oprd_of_pexpr ii e in
     ciok (MOV dst src)

  | Lopn ds op es => assemble_sopn ii ds op es

  | Llabel lbl => ciok (LABEL lbl)

  | Lgoto lbl => ciok (JMP lbl)

  | Lcond e l =>
      Let cond := assemble_cond ii e in
      ciok (Jcc l cond)
  end.

(* -------------------------------------------------------------------- *)
Definition assemble_c (lc: lcmd) : ciexec (seq asm) :=
  mapM assemble_i lc.

(* -------------------------------------------------------------------- *)
Definition assemble_fd (fd: lfundef) :=
  Let fd' := assemble_c (lfd_body fd) in

  match (reg_of_string (lfd_nstk fd)) with
  | Some sp =>
      Let arg := reg_of_vars xH (lfd_arg fd) in
      Let res := reg_of_vars xH (lfd_res fd) in
      ciok (XFundef (lfd_stk_size fd) sp arg fd' res)

  | None =>
      cierror xH (Cerr_assembler (AsmErr_string "Invalid stack pointer"))
  end.

(* -------------------------------------------------------------------- *)
Definition assemble_prog (p: lprog) : cfexec xprog :=
  map_cfprog assemble_fd p.
