(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.

(* -------------------------------------------------------------------- *)
Notation onth s n := (nth None (map Some s) n).

Definition oseq {T : Type} (s : seq (option T)) :=
  if size s == size (pmap idfun s) then Some (pmap idfun s) else None.

(* -------------------------------------------------------------------- *)
Parameter var : Type.
Parameter mem : Type.

Parameter CF : var.

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

Inductive cmd_name := ADDC.

Definition cmd : Type := cmd_name * seq var * seq var.

Parameter addc : int * int * bool -> int * bool.

Definition sem_addc_val (args : seq value) :=
  if args is [:: VInt x; VInt y; VBool c] then
     let: (z, c) := addc (x, y, c) in Some [:: VInt z; VBool c]
  else None.

Definition sem_addc (m : mem) (outv : seq var) (inv : seq var) :=
  if sem_addc_val [seq get m x | x <- inv] is Some res then
    sets m outv res
  else None.

Definition semc (m : mem) (c : cmd) : option mem :=
  match c with
  | (ADDC, outv, inv) => sem_addc m outv inv
  end.

(* -------------------------------------------------------------------- *)
Inductive arg_desc :=
| ADImplicit of var
| ADExplicit of nat.

Record instr_desc := {
  id_name : cmd_name;
  id_in   : seq arg_desc;
  id_out  : seq arg_desc;
}.

Definition locmd : Type := cmd_name * seq var.

Definition sem_ad (ad : arg_desc) (xs : seq var) : option var :=
  match ad with
  | ADImplicit x => Some x
  | ADExplicit n => onth xs n
  end.

Definition sem_id
  (m : mem) (id : instr_desc) (xs : seq var) : option mem
:=
  let: inx  := oseq [seq sem_ad ad xs | ad <- id.(id_in )] in
  let: outx := oseq [seq sem_ad ad xs | ad <- id.(id_out)] in

  if (inx, outx) is (Some inx, Some outx) then
    match id.(id_name) with
    | ADDC => sem_addc m outx inx
    end
  else None.

(* -------------------------------------------------------------------- *)
Definition ADDC_desc := {|
  id_name := ADDC;
  id_in   := [:: ADExplicit 0; ADExplicit 1; ADImplicit CF];
  id_out  := [:: ADExplicit 0; ADImplicit CF];
|}.

(* -------------------------------------------------------------------- *)
Definition get_id (c : cmd_name) :=
  match c with
  | ADDC => ADDC_desc
  end.

(* -------------------------------------------------------------------- *)
Lemma get_id_ok c : (get_id c).(id_name) = c.
Proof. by case: c. Qed.

(* -------------------------------------------------------------------- *)
Definition check_cmd_arg (ad : arg_desc) (args : seq var) :=
  match ad with
  | ADImplicit _ => true
  | ADExplicit n => n < size args
  end.

(* -------------------------------------------------------------------- *)
Definition check_cmd_args (c : cmd_name) (args : seq var) :=
  let: id := get_id c in
  all (check_cmd_arg^~ args) (id.(id_in) ++ id.(id_out)).
