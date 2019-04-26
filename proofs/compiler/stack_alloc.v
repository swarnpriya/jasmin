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

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word utils type var expr low_memory sem.
Require Import constant_prop.
Require Import compiler_util.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Record sfundef := MkSFun {
  sf_iinfo  : instr_info;
  sf_stk_sz : Z;
  sf_stk_id : Ident.ident;
  sf_tyin  : seq stype;
  sf_params : seq var_i;
  sf_body   : cmd;
  sf_tyout : seq stype;
  sf_res    : seq var_i;
}.

Definition sfundef_beq fd1 fd2 :=
  match fd1, fd2 with
  | MkSFun ii1 sz1 id1 ti1 p1 c1 to1 r1, MkSFun ii2 sz2 id2 ti2 p2 c2 to2 r2 =>
    (ii1 == ii2) && (sz1 == sz2) && (id1 == id2) &&
    (ti1 == ti2) && (p1 == p2) && (c1 == c2) && (to1 == to2) && (r1 == r2)
  end.

Lemma sfundef_eq_axiom : Equality.axiom sfundef_beq.
Proof.
  move=> [i1 s1 id1 ti1 p1 c1 to1 r1] [i2 s2 id2 ti2 p2 c2 to2 r2] /=.
  apply (@equivP ((i1 == i2) && (s1 == s2) && (id1 == id2) && (ti1 == ti2) && (p1 == p2) && (c1 == c2) && (to1 == to2) && (r1 == r2)));first by apply idP.
  by split=> [ /andP[] /andP[] /andP[] /andP[] /andP[] /andP[] /andP[] | [] ] /eqP -> /eqP->/eqP->/eqP->/eqP->/eqP->/eqP-> /eqP ->.
Qed.

Definition sfundef_eqMixin   := Equality.Mixin sfundef_eq_axiom.
Canonical  sfundef_eqType      := Eval hnf in EqType sfundef sfundef_eqMixin.

Record sprog := 
  { sp_rip   : Ident.ident;
    sp_globs : seq u8;
    sp_funcs : seq (funname * sfundef) }.

Record map := MkMap
  { mstk : Mvar.t Z;
    rsp : Ident.ident;
    mglob: Mvar.t Z;
    rip : Ident.ident; }.

Definition size_of (t:stype) := 
  match t with
  | sword sz => ok (wsize_size sz)
  | sarr n   => ok (Zpos n)
  | _      => cerror (Cerr_stk_alloc "size_of")
  end.

Definition aligned_for (ty: stype) (ofs: Z) : bool :=
  match ty with
  | sarr _ => true
  | sword sz => is_align (wrepr _ ofs) sz
  | sbool | sint => false
  end.

Definition init_map (sz:Z) (l:list (var * Z)):=
  let add (vp:var*Z) (mp:Mvar.t Z * Z) :=
      let '(v, p) := vp in
    if (mp.2 <=? p)%Z then
      let ty := vtype v in
      if aligned_for ty vp.2 then
      Let s := size_of ty in
      cok (Mvar.set mp.1 v p, p + s)%Z
    else cerror (Cerr_stk_alloc "not aligned")
    else cerror (Cerr_stk_alloc "overlap") in
  Let mp := foldM add (Mvar.empty Z, 0%Z) l in 
  if (mp.2 <=? sz)%Z then cok mp.1
  else cerror (Cerr_stk_alloc "stack size").

Definition is_in_stk (m:map) (x:var) :=
  match Mvar.get m.(mstk) x with 
  | Some _ => true
  | None   => false
  end.

Definition vrsp (m:map) :=  {|vtype := sword Uptr; vname := m.(rsp)|}.

Definition is_vrsp (m:map) (x:var) :=
  x == (vrsp m).

Definition vrip (m:map) :=  {|vtype := sword Uptr; vname := m.(rip)|}.

Definition is_vrip (m:map) (x:var) :=
  x == (vrip m).

Definition check_var m (x:var_i) := 
  ~~ is_in_stk m x && ~~is_vrsp m x && ~~is_vrip m x.

(* TODO: move *)
Definition is_word_type (t:stype) :=
  if t is sword sz then Some sz else None.

Definition cast_w ws := Papp1 (Oword_of_int ws).

Definition cast_ptr := cast_w Uptr.

Definition cast_const z := cast_ptr (Pconst z).

Definition mul := Papp2 (Omul (Op_w Uptr)).
Definition add := Papp2 (Oadd (Op_w Uptr)).

Definition cast_word e := 
  match e with
  | Papp1 (Oint_of_word U64) e1 => e1
  | _  => cast_ptr e
  end.

(* End TODO *)

Definition check_vfresh m x := 
  if is_glob x then cerror (Cerr_stk_alloc "global variable remain")
  else if is_vrsp m x.(gv) then cerror (Cerr_stk_alloc "the stack variable is not fresh")
  else if is_vrip m x.(gv) then cerror (Cerr_stk_alloc "the instruction pointer variable is not fresh")
  else ok tt.

Definition not_aligned {A} := 
  @cerror (Cerr_stk_alloc "array variable not aligned") A.

Definition invalid_var {A} := 
  @cerror (Cerr_stk_alloc "invalid variable") A.

Definition not_a_word_v {A} := 
  @cerror (Cerr_stk_alloc "not a word variable") A.

Definition mk_ofs ws e1 ofs := 
  let sz := wsize_size ws in
  if is_const e1 is Some i then 
    cast_const (i * sz + ofs)%Z
  else 
    add (mul (cast_const sz) (cast_word e1)) (cast_const ofs).

Definition find_gvar (m:map) (x:gvar) := 
  let m := if is_lvar x then m.(mstk) else m.(mglob) in
  match Mvar.get m x.(gv) with
  | Some ofs => Some ofs
  | None     => None
  end.

Definition vptr m (x:gvar) := if is_lvar x then vrsp m else vrip m.
   
Fixpoint alloc_e (m:map) (e: pexpr) := 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => ok e
  | Pvar   x =>
    match find_gvar m x with 
    | Some ofs =>
      let xv := x.(gv) in
      if is_word_type (vtype xv) is Some ws then
        let ofs := cast_const ofs in
        let stk := {| v_var := vptr m x; v_info := xv.(v_info) |} in
        ok (Pload ws stk ofs)
      else not_a_word_v 
    | None     =>
      Let _ := check_vfresh m x in
      ok e
    end
  | Pget ws x e1 =>
    Let e1 := alloc_e m e1 in
    match find_gvar m x with 
    | Some ofs =>
      if is_align (wrepr _ ofs) ws then 
        let stk := {| v_var := vptr m x; v_info := x.(gv).(v_info) |} in
        let ofs := mk_ofs ws e1 ofs in
        ok (Pload ws stk ofs)
      else not_aligned

    | None =>
      Let _ := check_vfresh m x in
      ok (Pget ws x e1)
    end

  | Pload ws x e1 =>
    if check_var m x then
      Let e1 := alloc_e m e1 in
      ok (Pload ws x e1)
    else invalid_var 

  | Papp1 o e1 =>
    Let e1 := alloc_e m e1 in
    ok (Papp1 o e1)
   
  | Papp2 o e1 e2 =>
    Let e1 := alloc_e m e1 in
    Let e2 := alloc_e m e2 in
    ok (Papp2 o e1 e2)

  | PappN o es => 
    Let es := mapM (alloc_e m) es in
    ok (PappN o es)  

  | Pif t e e1 e2 =>
    Let e := alloc_e m e in
    Let e1 := alloc_e m e1 in
    Let e2 := alloc_e m e2 in
    ok (Pif t e e1 e2)
  end.

Definition alloc_lval (m:map) (r:lval) ty := 
  match r with
  | Lnone _ _ => ok r

  | Lvar x =>
    match Mvar.get m.(mstk) x with 
    | Some ofs =>
      if is_word_type (vtype x) is Some ws then
        if ty == sword ws then  
          let ofs := cast_const ofs in
          let stk := {| v_var := vrsp m; v_info := x.(v_info) |} in
          ok (Lmem ws stk ofs)
        else cerror (Cerr_stk_alloc "invalid type for Lvar")
      else not_a_word_v 
    | None     =>
      Let _ := check_vfresh m (mk_lvar x) in
      ok r
    end

  | Lmem ws x e1 =>
    if check_var m x then
      Let e1 := alloc_e m e1 in
      ok (Lmem ws x e1)
    else invalid_var
    
  | Laset ws x e1 =>
    Let e1 := alloc_e m e1 in
    match Mvar.get m.(mstk) x with 
    | Some ofs =>
      if is_align (wrepr _ ofs) ws then
        let stk := {| v_var := vrsp m; v_info := x.(v_info) |} in
        let ofs := mk_ofs ws e1 ofs in
        ok (Lmem ws stk ofs)
      else not_aligned

    | None =>
      Let _ := check_vfresh m (mk_lvar x) in
      ok (Laset ws x e1)
    end

  end.

Definition bad_lval_number := Cerr_stk_alloc "invalid number of lval".

Fixpoint alloc_i (m: map) (i: instr) :=
  let (ii, ir) := i in
  Let ir := 
    match ir with
    | Cassgn r t ty e => 
      Let r := add_iinfo ii (alloc_lval m r ty) in
      Let e := add_iinfo ii (alloc_e m e) in
      ok (Cassgn r t ty e)
  
    | Copn rs t o e => 
      Let rs := add_iinfo ii (mapM2 bad_lval_number (alloc_lval m) rs (sopn_tout o)) in
      Let e  := add_iinfo ii (mapM  (alloc_e m) e) in
      ok (Copn rs t o e)               
  
    | Cif e c1 c2 => 
      Let e := add_iinfo ii (alloc_e m e) in
      Let c1 := mapM (alloc_i m) c1 in
      Let c2 := mapM (alloc_i m) c2 in
      ok (Cif e c1 c2)
  
    | Cwhile a c1 e c2 => 
      Let e := add_iinfo ii (alloc_e m e) in
      Let c1 := mapM (alloc_i m) c1 in
      Let c2 := mapM (alloc_i m) c2 in
      ok (Cwhile a c1 e c2)
  
    | Cfor _ _ _  => cierror ii (Cerr_stk_alloc "don't deal with for loop")
    | Ccall _ _ _ _ => cierror ii (Cerr_stk_alloc "don't deal with call")
    end in
  ok (MkI ii ir).


Definition add_err_fun (A : Type) (f : funname) (r : cexec A) := 
  match r with
  | ok _ a => ok a
  | Error e => Error (Ferr_fun f e)
  end.

Definition alloc_fd rip mglob (stk_alloc_fd : fun_decl -> Z * Ident.ident * list (var * Z))
    (f: fun_decl) :=
  let info := stk_alloc_fd f in
  let (fn, fd) := f in
  Let sfd :=  
    let: ((size, rsp), l) := info in 
    Let mstk := add_err_fun fn (init_map size l) in
    let m :=  
        {| mstk  := mstk;
           rsp   := rsp;
           mglob := mglob;
           rip   := rip |} in
    Let body := add_finfo fn fn (mapM (alloc_i m) fd.(f_body)) in
    if (rsp != rip) && all (check_var m) fd.(f_params) && all (check_var m) fd.(f_res) then
      ok {| sf_iinfo  := fd.(f_iinfo);
            sf_stk_sz := size;
            sf_stk_id := rsp;
            sf_tyin   := fd.(f_tyin);
            sf_params := fd.(f_params);
            sf_body   := body;
            sf_tyout  := fd.(f_tyout);
            sf_res    := fd.(f_res) |} 
    else add_err_fun fn invalid_var in
  ok (fn, sfd).

Definition check_glob (m: Mvar.t Z) (data:seq u8) (gd:glob_decl) := 
  let x := gd.1 in
  match Mvar.get m x with
  | None => false 
  | Some z =>
    let n := Z.to_nat z in
    let data := drop n data in
    match gd.2 with
    | @Gword ws w =>
      let s := Z.to_nat (wsize_size ws) in 
      (s <= size data) && 
      (LE.decode ws (take s data) == w)
    | @Garr p t =>
      let s := Z.to_nat p in
      (s <= size data) &&
      all (fun i => 
             match WArray.get U8 t (Z.of_nat i) with
             | Ok w => nth 0%R data i == w
             | _    => false
             end) (iota 0 s)
     end
  end.

Definition check_globs (gd:glob_decls) (m:Mvar.t Z) (data:seq u8) := 
  all (check_glob m data) gd.

Definition alloc_prog stk_alloc_fd (glob_alloc_p : prog -> seq u8 * Ident.ident * list (var * Z) ) P := 
  let: ((data, rip), l) := glob_alloc_p P in 
  Let mglob := add_err_msg (init_map (Z.of_nat (size data)) l) in
  if check_globs P.(p_globs) mglob data then
    Let p_funs := mapM (alloc_fd rip mglob stk_alloc_fd) P.(p_funcs) in
    ok  {| sp_rip   := rip; 
           sp_globs := data; 
           sp_funcs := p_funs |}
  else 
     Error (Ferr_msg (Cerr_stk_alloc "invalid data: please report")).
    



