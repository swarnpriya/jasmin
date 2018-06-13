Require Ssem.

Import Utf8.
Import Morphisms.
Import all_ssreflect.
Import ZArith.
Local Open Scope Z_scope.

Import utils.
Import type.
Import var.
Import expr.
Import sem.
Import Ssem.
Import low_memory.
Import UnsafeMemory.
Import psem.

(* Problem : Sij'ai pas exemple (x := 3; y := x) ; While (true) ·{ } alors le programme considere que j'ai besoin de x...*)

Function Sv_of_var (r:lval) :=
  match r with
  | Lnone _ _  => Sv.empty
  | Lvar x     => Sv.singleton x
  | Lmem _ x _ => Sv.singleton x 
  | Laset x _  => Sv.singleton x
  end.

Fixpoint Sv_of_vars (s : lvals) :=
  match s with
  |[::]  => Sv.empty
  |r::s' => Sv.union (Sv_of_var r) (Sv_of_vars s')
  end.

(*Function foldl_bs s :=
  match s with
  |[::]  => (true,Sv.empty)
  |(b1,s1)::s' => let (b2,s2) := foldl_bs s' in
                  (b1 && b2, Sv.union s1 s2)
  end.*)

Fixpoint test_init_rec_i (bs : bool*Sv.t) (i : instr_r) {struct i} :=
  let (b,s) := bs in
  match i with
  |Cif bif c1 c2    => let s' := read_e bif in
                       let b' := Sv.subset s' s in
                       let (b1,s1) := foldl test_init_rec_I bs c1 in
                       let (b2,s2) := foldl test_init_rec_I bs c2 in
                       let sv := Sv.inter s1 s2 in
                       (b && b' && b1 && b2, sv)
  |Cfor x r c       => let (r,e1) := r in
                       let (_,e2) := r in
                       let s1 := read_e e1 in
                       let s2 := read_e e2 in
                       let b1 := Sv.subset s1 s in
                       let b2 := Sv.subset s2 s in
                       let (b', _) := foldl test_init_rec_I bs c in
                       (b && b' && b1 && b2, s)
  |Cwhile c e c'    => let (b', s') := foldl test_init_rec_I bs c in
                       let se := read_e e in
                       let be := Sv.subset se s' in
                       let (b'', _) := foldl test_init_rec_I (b,s') c' in
                       (b && be && b' && b'', s')
  | Cassgn x _ _ e  => let s' := read_e e in
                       let b' := Sv.subset s' s in
                       (b && b',Sv.union (Sv_of_var x) s)
  | Copn xs _ _ es  => let s' := read_es es in
                       let b' := Sv.subset s' s in
                       let sv := Sv.union (Sv_of_vars xs) s in
                       (b && b', sv)
  | Ccall _ xs _ es => let s' := read_es es in
                       let b' := Sv.subset s' s in
                       let sv := Sv.union (Sv_of_vars xs) s in
                       (b && b', sv)
  end with
test_init_rec_I (bs: bool * Sv.t) (i : instr) {struct i} :=
  let: MkI _ i := i in test_init_rec_i bs i.


Definition test_init (c : cmd) := foldl test_init_rec_I (true,Sv.empty) c.

Let var_info_x : var_info := 1%positive.
Let var_info_y : var_info := 2%positive.
Let var_info_z : var_info := 3%positive.

Let var_x := Var sint "x".
Let var_y := Var sint "y".
Let var_z := Var sint "z".

Let var_i_x := VarI var_x var_info_x.
Let var_i_y := VarI var_y var_info_y.
Let var_i_z := VarI var_z var_info_z.

Let x := Lvar var_i_x.
Let y := Lvar var_i_y.
Let z := Lvar var_i_z.

Let e_y := Pvar var_i_y.
Let e_3 := Pconst 3.
Let etrue  := Pbool true.
Let efalse := Pbool false.

Axiom tag1 : assgn_tag.
Axiom tag2 : assgn_tag.
Axiom tag3 : assgn_tag.

Axiom instri1 : instr_info.
Axiom instri2 : instr_info.
Axiom instri3 : instr_info.
Axiom instri4 : instr_info.
Axiom instri5 : instr_info.
Axiom instri6 : instr_info.

Let iasgn_y_3 := Cassgn y tag2 sint e_3.
Let iasgn_x_y := Cassgn x tag1 sint e_y.


Let asgn_x_y := MkI instri2 iasgn_x_y.
Let asgn_y_3 := MkI instri1 iasgn_y_3.

Let c_null : cmd := [::].
Let c_x_y  : cmd := asgn_x_y::[::].
Let c_y_3  : cmd := asgn_y_3::[::].
Let c_y_3_x_y  : cmd := asgn_y_3::asgn_x_y::[::].


Let iasgn_if_true := Cif etrue c_y_3 c_null.
Let asgn_if_true := MkI instri3 iasgn_if_true.
Let iasgn_if_true2 := Cif etrue c_y_3 c_y_3.
Let asgn_if_true2 := MkI instri3 iasgn_if_true2.

Let iasgn_while_true := Cwhile c_null etrue c_y_3.
Let asgn_while_true := MkI instri4 iasgn_while_true.
Let iasgn_while_true_init := Cwhile c_y_3 etrue c_null.
Let asgn_while_true_init := MkI instri5 iasgn_while_true_init.

Let c_init_use :=  asgn_while_true_init :: c_x_y.

Let test_cif := asgn_if_true :: asgn_x_y :: [::].
Let test_cif2 := asgn_if_true2 :: asgn_x_y :: [::].
Let test_cwhile1 := asgn_while_true :: asgn_x_y :: [::].
Let test_cwhile_init := asgn_while_true_init :: [::].

Let test_init_used_in_condition := MkI instri6 (Cwhile c_y_3_x_y etrue  c_null) :: [::]. 

Eval vm_compute in (test_init test_cwhile_init).

Lemma sem_I_sem_c p gd s1 i s2:
      sem_I p gd s1 i s2 -> sem p gd s1 [::i] s2.
move => E; exact: Eseq E (Eskip p gd s2).
Qed.

(*Theorem test_init_mem s1 s' c p gd :
  sem p gd s1 c s' ->
  (exists sv, test_init c = (true,sv)) ->
  forall s2, sem p gd s2 c s'.
Proof.
  move:s1 s';induction c.
  move => s1 s' E.
  inversion E;subst.
  move => [sv].
  
  move => _ s2.
  
  Theorem test_init_true s1 s2 (c:cmd) p gd :
  sem p gd s1 c s2 -> exists s, test_init c = (true, s).
Proof.
move:s1 s2. induction c;first by exists Sv.empty.
move => s1 s3.
case:a => ii;case => [x tag st e | x tag O e | e c1 c2 | xi r c1 | c1 e c2 | inl xs fn es] E;inversion E => {E};subst;
move:H4 => /IHc [s] test_s; apply sem_I_sem_c in H2.
rewrite /test_init.
apply IHc.
apply IHc in H2.
Qed.*)