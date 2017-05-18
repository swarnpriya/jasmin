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
From mathcomp Require Import all_ssreflect.
Require Import expr ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope vmap_scope.
Local Open Scope Z_scope.
(* -------------------------------------------------------------------------- *)
(* ** Smart constructors                                                      *)
(* -------------------------------------------------------------------------- *)

Definition snot_bool (e:pexpr) := 
  match e with
  | Pbool b      => negb b
  | Papp1 Onot e => e 
  | _            => Papp1 Onot e
  end.

(* FIXME: make this smart constructor smarter *)
Definition sneg (e: pexpr) := Papp1 Oneg e.

Definition sand e1 e2 := 
  match is_bool e1, is_bool e2 with
  | Some b, _ => if b then e2 else false
  | _, Some b => if b then e1 else false
  | _, _      => Papp2 Oand e1 e2
  end.

Definition sor e1 e2 := 
   match is_bool e1, is_bool e2 with
  | Some b, _ => if b then Pbool true else e2
  | _, Some b => if b then Pbool true else e1
  | _, _       => Papp2 Oor e1 e2 
  end.

(* FIXME improve this *)
Definition snot_w ws e := Papp1 (Olnot ws) e.

Definition s_op1 o e := 
  match o with
  | Onot  => snot_bool e 
  | Olnot ws => snot_w ws e
  | Oneg => sneg e
  end.

(* ------------------------------------------------------------------------ *)

Definition tobase (wz:wsize * Z) : Z :=
  match wz.1 with
  | U8  => I8 .unsigned (I8 .repr wz.2)
  | U16 => I16.unsigned (I16.repr wz.2)
  | U32 => I32.unsigned (I32.repr wz.2)
  | U64 => I64.unsigned (I64.repr wz.2)
  end.

Definition sadd_int e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 + n2)
  | Some n, _ => 
    if (n == 0)%Z then e2 else Papp2 (Oadd Op_int) e1 e2
  | _, Some n => 
    if (n == 0)%Z then e1 else Papp2 (Oadd Op_int) e1 e2
  | _, _ => Papp2 (Oadd Op_int) e1 e2
  end.


Definition tobase2 ws wz := 
  tobase (ws, tobase wz).

Definition sadd_w ws e1 e2 := 
  match is_wconst e1, is_wconst e2 with
  | Some n1, Some n2 => 
    wconst (ws ,iword_wadd ws (tobase n1) (tobase n2))
  | Some n, _ => 
    if (tobase2 ws n == 0)%Z then e2 else Papp2 (Oadd (Op_w ws)) e1 e2
  | _, Some n => 
    if (tobase2 ws n == 0)%Z then e1 else Papp2 (Oadd (Op_w ws)) e1 e2
  | _, _ => Papp2 (Oadd (Op_w ws)) e1 e2
  end.

Definition sadd ty :=
  match ty with
  | Op_int  => sadd_int
  | Op_w ws => sadd_w ws
  end.

Definition ssub_int e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 - n2)
  | _, Some n => 
    if (n == 0)%Z then e1 else Papp2 (Osub Op_int) e1 e2
  | _, _ => Papp2 (Osub Op_int) e1 e2
  end.

Definition ssub_w ws e1 e2 := 
  match is_wconst e1, is_wconst e2 with
  | Some n1, Some n2 => wconst (ws, (iword_wsub ws (tobase n1) (tobase n2)))
  | _, Some n => 
    if (tobase2 ws n == 0)%Z then e1 else Papp2 (Osub (Op_w ws)) e1 e2
  | _, _ => Papp2 (Osub (Op_w ws)) e1 e2
  end.

Definition ssub ty := 
  match ty with
  | Op_int  => ssub_int
  | Op_w ws => ssub_w ws
  end.

Definition smul_int e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 * n2)
  | Some n, _ => 
    if (n == 0)%Z then Pconst 0
    else if (n == 1)%Z then e2 
    else Papp2 (Omul Op_int) e1 e2
  | _, Some n => 
    if (n == 0)%Z then Pconst 0
    else if (n == 1)%Z then e1
    else Papp2 (Omul Op_int) e1 e2
  | _, _ => Papp2 (Omul Op_int) e1 e2
  end.

Definition smul_w ws e1 e2 := 
  match is_wconst e1, is_wconst e2 with
  | Some n1, Some n2 => wconst (ws, iword_wmul ws (tobase n1) (tobase n2))
  | Some n, _ => 
    let n := tobase2 ws n in
    if (n == 0)%Z then wconst (ws, 0)
    else if (n == 1)%Z then e2 
    else Papp2 (Omul (Op_w ws)) (wconst (ws, n)) e2
  | _, Some n => 
    let n := tobase2 ws n in
    if (n == 0)%Z then wconst (ws, 0)
    else if (n == 1)%Z then e1
    else Papp2 (Omul (Op_w ws)) e1 (wconst (ws, n))
  | _, _ => Papp2 (Omul (Op_w ws)) e1 e2
  end.

Definition smul ty := 
  match ty with
  | Op_int  => smul_int
  | Op_w ws => smul_w ws
  end.

Definition s_eq ty e1 e2 := 
  if eq_expr e1 e2 then Pbool true 
  else 
    match ty with
    | Cmp_int =>
      match is_const e1, is_const e2 with
      | Some i1, Some i2 => Pbool (i1 == i2)
      | _, _             => Papp2 (Oeq ty) e1 e2
      end 
    | Cmp_sw ws | Cmp_uw ws =>
      match is_wconst e1, is_wconst e2 with
      | Some i1, Some i2 => Pbool (iword_weq ws (tobase i1) (tobase i2))
      | _, _             => Papp2 (Oeq ty) e1 e2
      end
    end.

Definition sneq ty e1 e2 := 
  match is_bool (s_eq ty e1 e2) with
  | Some b => Pbool (~~ b)
  | None   => Papp2 (Oneq ty) e1 e2
  end.

(* FIXME Improve this *)

Definition slt ty e1 e2 := 
  if eq_expr e1 e2 then Pbool false 
  else match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 <? n2)%Z
  | _      , _       => Papp2 (Olt ty) e1 e2 
  end.

Definition sle ty e1 e2 := 
  if eq_expr e1 e2 then Pbool true 
  else match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 <=? n2)%Z
  | _      , _       => Papp2 (Ole ty) e1 e2 
  end.

Definition sgt ty e1 e2 := 
  if eq_expr e1 e2 then Pbool false 
  else match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 >? n2)%Z
  | _      , _       => Papp2 (Ogt ty) e1 e2 
  end.

Definition sge ty e1 e2 := 
  if eq_expr e1 e2 then Pbool true 
  else match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 >=? n2)%Z
  | _      , _       => Papp2 (Oge ty) e1 e2 
  end.

(* FIXME: Improve this *)

Definition sland ws e1 e2 := Papp2 (Oland ws) e1 e2.
Definition slor  ws e1 e2 := Papp2 (Olor  ws) e1 e2.
Definition slxor ws e1 e2 := Papp2 (Olxor ws) e1 e2.
Definition slsr  ws e1 e2 := Papp2 (Olsr  ws) e1 e2.
Definition slsl  ws e1 e2 := Papp2 (Olsl  ws) e1 e2.
Definition sasr  ws e1 e2 := Papp2 (Oasr  ws) e1 e2.

Definition s_op2 o e1 e2 := 
  match o with 
  | Oand     => sand     e1 e2 
  | Oor      => sor      e1 e2
  | Oadd  ty => sadd  ty e1 e2
  | Osub  ty => ssub  ty e1 e2
  | Omul  ty => smul  ty e1 e2
  | Oeq   ty => s_eq  ty e1 e2
  | Oneq  ty => sneq  ty e1 e2
  | Olt   ty => slt   ty e1 e2
  | Ole   ty => sle   ty e1 e2
  | Ogt   ty => sgt   ty e1 e2
  | Oge   ty => sge   ty e1 e2
  | Oland ws => sland ws e1 e2
  | Olor  ws => slor  ws e1 e2
  | Olxor ws => slxor ws e1 e2 
  | Olsr  ws => slsr  ws e1 e2
  | Olsl  ws => slsl  ws e1 e2
  | Oasr  ws => sasr  ws e1 e2
  end.

Definition s_if e e1 e2 := 
  match is_bool e with
  | Some b => if b then e1 else e2
  | None   => Pif e e1 e2
  end.

(* ** constant propagation 
 * -------------------------------------------------------------------- *)

Local Notation cpm := (Mvar.t Z).

Fixpoint const_prop_e (m:cpm) e :=
  match e with
  | Pconst _      => e
  | Pbool  _      => e
  | Pcast ws e    => Pcast ws (const_prop_e m e)
  | Pvar  x       => if Mvar.get m x is Some n then Pconst n else e
  | Pget  x e     => Pget x (const_prop_e m e)
  | Pload ws x e  => Pload ws x (const_prop_e m e)
  | Papp1 o e     => s_op1 o (const_prop_e m e)
  | Papp2 o e1 e2 => s_op2 o (const_prop_e m e1)  (const_prop_e m e2)
  | Pif e e1 e2   => s_if (const_prop_e m e) (const_prop_e m e1) (const_prop_e m e2)
  end.

Definition empty_cpm : cpm := @Mvar.empty Z.

Definition merge_cpm : cpm -> cpm -> cpm := 
  Mvar.map2 (fun _ (o1 o2: option Z) => 
   match o1, o2 with
   | Some n1, Some n2 => 
     if (n1 == n2)%Z then Some n1
     else None
   | _, _ => None
   end).

Definition remove_cpm (m:cpm) (s:Sv.t): cpm :=
  Sv.fold (fun x m => Mvar.remove m x) s m.

Definition const_prop_rv (m:cpm) (rv:lval) : cpm * lval := 
  match rv with 
  | Lnone _ _ => (m, rv)
  | Lvar  x   => (Mvar.remove m x, rv)
    (* TODO : FIXME should we do more on x, in particular if x is a known value *)
  | Lmem ws x e => (m, Lmem ws x (const_prop_e m e))
  | Laset x e => (Mvar.remove m x, Laset x (const_prop_e m e))
  end.

Fixpoint const_prop_rvs (m:cpm) (rvs:lvals) : cpm * lvals := 
  match rvs with
  | [::] => (m, [::])
  | rv::rvs => 
    let (m,rv)  := const_prop_rv m rv in 
    let (m,rvs) := const_prop_rvs m rvs in
    (m, rv::rvs)
  end.

Definition add_cpm (m:cpm) (rv:lval) tag e := 
  if rv is Lvar x then
    if tag is AT_inline then 
      if is_const e is Some n then Mvar.set m x n else m 
    else m
  else m. 
                           
Section CMD.

  Variable const_prop_i : cpm -> instr -> cpm * cmd.

  Fixpoint const_prop (m:cpm) (c:cmd) : cpm * cmd :=
    match c with
    | [::] => (m, [::])
    | i::c =>
      let (m,ic) := const_prop_i m i in
      let (m, c) := const_prop m c in
      (m, ic ++ c)
    end.

End CMD.

Fixpoint const_prop_ir (m:cpm) ii (ir:instr_r) : cpm * cmd := 
  match ir with
  | Cassgn x tag e => 
    let e := const_prop_e m e in 
    let (m,x) := const_prop_rv m x in
    let m := add_cpm m x tag e in
    (m, [:: MkI ii (Cassgn x tag e)])

  | Copn xs o es =>
    let es := map (const_prop_e m) es in
    let (m,xs) := const_prop_rvs m xs in
    (m, [:: MkI ii (Copn xs o es) ])

  | Cif b c1 c2 => 
    let b := const_prop_e m b in
    match is_bool b with
    | Some b => 
      let c := if b then c1 else c2 in 
      const_prop const_prop_i m c
    | None =>
      let (m1,c1) := const_prop const_prop_i m c1 in
      let (m2,c2) := const_prop const_prop_i m c2 in
      (merge_cpm m1 m2, [:: MkI ii (Cif b c1 c2) ])
    end

  | Cfor x (dir, e1, e2) c =>
    let e1 := const_prop_e m e1 in
    let e2 := const_prop_e m e2 in
    let m := remove_cpm m (write_i ir) in
    let (_,c) := const_prop const_prop_i m c in
    (m, [:: MkI ii (Cfor x (dir, e1, e2) c) ])

  | Cwhile c e c' =>
    let m := remove_cpm m (write_i ir) in
    let (_,c) := const_prop const_prop_i m c in
    let (_,c') := const_prop const_prop_i m c' in
    (m, [:: MkI ii (Cwhile c (const_prop_e m e) c')])

  | Ccall fi xs f es =>
    let es := map (const_prop_e m) es in
    let (m,xs) := const_prop_rvs m xs in
    (m, [:: MkI ii (Ccall fi xs f es) ])
  end

with const_prop_i (m:cpm) (i:instr) : cpm * cmd :=
  let (ii,ir) := i in
  const_prop_ir m ii ir.

Definition const_prop_fun (f:fundef) :=
  let (ii,p,c,r) := f in
  let (_, c) := const_prop const_prop_i empty_cpm c in
  MkFun ii p c r.

Definition const_prop_prog (p:prog) : prog := map_prog const_prop_fun p.

