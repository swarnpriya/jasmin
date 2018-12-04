open Utils
open Prog
open Apron
open ToEC
open Type

exception Aint_error of string

(* let () = Glob_options.debug := true *)

let debug a = if !Glob_options.debug then a () else ()

let () = debug (fun () -> Printexc.record_backtrace true)

(***********************)
(* Analysis Parameters *)
(***********************)

(* Number of unrolling of a loop body before applying the widening. Higher values
   yield a more precise (and more costly) analysis. *)
let k_unroll = 0;;

assert (k_unroll >= 0)

(* Rounding used. *)
let round_typ = Texpr1.Zero

(* Analysis strategy when for abstract calls. *)
type abs_call_strategy =
  | CallDirect
  | CallWidening

let abs_call_strategy = CallDirect


(*************************)
(* Unique Variable Names *)
(*************************)

module MkUniq : sig

  val mk_uniq : unit func -> unit prog -> (unit func * unit prog)

end = struct
  let ht_uniq = Hashtbl.create ~random:false 16

  let htv = Hashtbl.create ~random:false 16

  let rec mk_uniq main_decl (glob_decls, fun_decls) =
    let m_decl = mk_f main_decl in
    (m_decl, (mk_globs glob_decls, List.map mk_f fun_decls))

  and mk_gv v = v ^ "##g"

  and mk_glob (ws, t, i) = (ws, mk_gv t, i)

  and mk_globs globs = List.map mk_glob globs

  and mk_f f_decl =
    { f_decl with
      f_args = List.map (mk_v f_decl.f_name.fn_name) f_decl.f_args;
      f_body = mk_stmt f_decl.f_name.fn_name f_decl.f_body;
      f_ret = List.map (mk_v_loc f_decl.f_name.fn_name) f_decl.f_ret }

  and mk_v fn v =
    if Hashtbl.mem htv (v.v_name, fn) then
      Hashtbl.find htv (v.v_name, fn)
    else if Hashtbl.mem ht_uniq v.v_name then
      let nv = V.mk (v.v_name ^ "#" ^ fn) v.v_kind v.v_ty v.v_dloc in
      let () = Hashtbl.add htv (v.v_name, fn) nv in
      nv
    else
      let () = Hashtbl.add ht_uniq v.v_name () in
      let () = Hashtbl.add htv (v.v_name, fn) v in
      v

  and mk_v_loc fn v = L.mk_loc (L.loc v) (mk_v fn (L.unloc v))

  and mk_lval fn lv = match lv with
    | Lnone _ -> lv
    | Lvar v -> Lvar (mk_v_loc fn v)
    | Lmem (ws,ty,e) -> Lmem (ws, mk_v_loc fn ty, mk_expr fn e)
    | Laset (v,e) -> Laset (mk_v_loc fn v, mk_expr fn e)

  and mk_range fn (dir, e1, e2) = (dir, mk_expr fn e1, mk_expr fn e2)

  and mk_lvals fn lvs = List.map (mk_lval fn) lvs

  and mk_instr fn st = { st with i_desc = mk_instr_r fn st.i_desc }

  and mk_instr_r fn st = match st with
    | Cassgn (lv, tag, ty, e) ->
      Cassgn (mk_lval fn lv, tag, ty, mk_expr fn e)
    | Copn (lvls, tag, opn, exprs) ->
      Copn (mk_lvals fn lvls, tag, opn, mk_exprs fn exprs)
    | Cif (e, st, st') ->
      Cif (mk_expr fn e, mk_stmt fn st, mk_stmt fn st')
    | Cfor (v, r, st) ->
      Cfor (mk_v_loc fn v, mk_range fn r, mk_stmt fn st)
    | Ccall (inlinf, lvs, c_fn, es) ->
      Ccall (inlinf, mk_lvals fn lvs, c_fn, mk_exprs fn es)
    | Cwhile (st1, e, st2) ->
      Cwhile (mk_stmt fn st1, mk_expr fn e, mk_stmt fn st2)

  and mk_stmt fn instrs = List.map (mk_instr fn) instrs

  and mk_expr fn expr = match expr with
    | Pconst _ | Pbool _ | Parr_init _ -> expr
    | Pglobal (ws,t) -> Pglobal (ws, mk_gv t)
    | Pcast (ws, e) -> Pcast (ws, mk_expr fn e)
    | Pvar v -> Pvar (mk_v_loc fn v)
    | Pget (v, e) -> Pget (mk_v_loc fn v, mk_expr fn e)
    | Pload (ws, v, e) -> Pload (ws, mk_v_loc fn v, mk_expr fn e)
    | Papp1 (op, e) -> Papp1 (op, mk_expr fn e)
    | Papp2 (op, e1, e2) -> Papp2 (op, mk_expr fn e1, mk_expr fn e2)
    | Pif (e, el, er)  -> Pif (mk_expr fn e, mk_expr fn el, mk_expr fn er)

  and mk_exprs fn exprs = List.map (mk_expr fn) exprs

end


(*******************)
(* Pretty Printers *)
(*******************)

let pp_apr_env ppf e = Environment.print ppf e;;

let rec pp_list ?sep:(msep = Format.pp_print_cut) pp_el fmt l = match l with
  | [] -> Format.fprintf fmt ""
  | h :: t -> Format.fprintf fmt "%a%a%a" pp_el h msep () (pp_list pp_el) t;;

let pp_opt pp_el fmt = function
  | None -> Format.fprintf fmt "None"
  | Some el -> Format.fprintf fmt "Some @[%a@]" pp_el el


(*************)
(* Profiling *)
(*************)

let rec assoc_up s f = function
  | [] -> raise Not_found
  | (a,b) :: t ->
    if a = s then (a, f b) :: t
    else (a,b) :: assoc_up s f t

module Prof : sig
  val record : string -> unit
  val call : string -> float -> unit

  val print : Format.formatter -> unit -> unit
end = struct
  let lrec = ref []

  let record s =
    let () = assert (not (List.mem_assoc s !lrec)) in
    lrec := (s,(0,0.)) :: !lrec;;

  let call s t =
    lrec := assoc_up s (fun (x,t') -> (x + 1,t +. t')) !lrec;;

  let print fmt () =
    let pp_el fmt (a, (b,f)) =
      Format.fprintf fmt "%10d %s : %1f seconds" b a f in

    Format.fprintf fmt "@[<v>Statistiques:@;@[<v>%a@]@]@."
      (pp_list pp_el) (List.sort (fun (a,(_,f)) (a',(_,f')) ->
                                       if a = a' then 0
                                       else if f > f' then -1 else 1) !lrec)
end


(************************)
(* Abstract Environment *)
(************************)

(* Memory locations *)
type mem_loc = MemLoc of ty gvar


type atype =
  | Avar of ty gvar             (* Variable *)
  | Aarray of ty gvar           (* Array *)
  | AarrayEl of ty gvar * int   (* Array element *)


(* - Temp : temporary variable
 * - WTemp : temporary variable (weak updates)
 * - Mglobal : global variable
 * - MinValue : variable initial value *)
type mvar =
  | Temp of string * int * ty
  | WTemp of string * int * ty
  | Mglobal of Name.t * ty
  | Mvalue of atype
  | MinValue of ty gvar
  | MvarOffset of ty gvar       (* Variable offset *)
  | MmemRange of mem_loc        (* Memory location range *)

let weak_update v = match v with
  | Mvalue _ | MinValue _  | Mglobal _
  | Temp _
  | MvarOffset _ -> false
  | MmemRange _ -> true
  | WTemp _ -> true

let string_of_mloc = function MemLoc s -> s.v_name

let string_of_atype = function
  | Avar s -> "v_" ^ s.v_name
  | Aarray t -> "a_" ^ t.v_name
  | AarrayEl (t,int) -> Format.asprintf "ael_%s_%d" t.v_name int

let string_of_mvar = function
  | Temp (s, i, _) -> "tmp_" ^ s ^ "_" ^ string_of_int i
  | WTemp (s, i, _) -> "wtmp_" ^ s ^ "_" ^ string_of_int i
  | Mglobal (n,_) -> "g_" ^ n
  | MinValue s -> "inv_" ^ s.v_name
  | Mvalue at -> string_of_atype at
  | MvarOffset s -> "o_" ^ s.v_name
  | MmemRange loc -> "rmem_" ^ string_of_mloc loc


let variables_ignore v =
  let vs = Var.to_string v in
  match String.split_on_char '_' vs with
  | "inv" :: _ | "ael" :: _  -> true
  | _ -> false

let arr_range v = match v.v_ty with
  | Arr (_,i) -> i
  | _ -> assert false

let arr_size v = match v.v_ty with
  | Arr (ws,_) -> ws
  | _ -> assert false

let ty_atype = function
  | Avar s -> s.v_ty
  | Aarray t -> t.v_ty
  | AarrayEl (t,_) -> let ws = arr_size t in Bty (U ws)

let ty_mvar = function
  | Temp (_,_,ty) -> ty
  | WTemp (_,_,ty) -> ty
  | Mglobal (_,ty) -> ty
  | MinValue s -> s.v_ty
  | Mvalue at -> ty_atype at
  | MvarOffset _ -> Bty Int
  | MmemRange _ -> Bty Int

let avar_of_mvar a = string_of_mvar a |> Var.of_string

let temp_cpy s i v = match v with
  | Mvalue _  | Mglobal _ | MmemRange _ | MvarOffset _
    -> Temp (s,i, ty_mvar v)
  | Temp _ | WTemp _
  | MinValue _ -> assert false

let rec expand_arr_vars = function
  | [] -> []
  | Mvalue (Aarray v) :: t -> begin match v.v_ty with
      | Bty _ -> assert false
      | Arr (_, n) -> List.init n (fun i -> Mvalue (AarrayEl (v,i)))
                      @ expand_arr_vars t end
  | v :: t -> v :: expand_arr_vars t

let rec expand_arr_tys = function
  | [] -> []
  | Arr (ws, n) :: t ->
    List.init n (fun _ -> Bty (U ws)) @ expand_arr_tys t
  | v :: t -> v :: expand_arr_tys t

let rec expand_arr_exprs = function
  | [] -> []
  | Pvar v :: t -> begin match (L.unloc v).v_ty with
      | Arr (_, n) ->
        List.init n (fun i -> Pget (v, Pconst (B.of_int i)))
        @ expand_arr_exprs t
      | _ -> Pvar v :: expand_arr_exprs t end
  | h :: t -> h :: expand_arr_exprs t


type apr_env = Apron.Environment.t


(******************)
(* Texpr1 Wrapper *)
(******************)

module Mmv = struct
  type t = mvar

  let compare v v' = Pervasives.compare (avar_of_mvar v) (avar_of_mvar v')
  let equal v v' = avar_of_mvar v = avar_of_mvar v'
end

module Mm = Map.Make(Mmv)

module Mtexpr : sig
  type unop = Texpr0.unop
  type binop = Texpr0.binop
  type typ = Apron.Texpr0.typ
  type round = Apron.Texpr0.round

  type mexpr = private
    | Mcst of Coeff.t
    | Mvar of mvar
    | Munop of unop * mexpr * typ * round
    | Mbinop of binop * mexpr * mexpr * typ * round

  type t = { mexpr : mexpr;
             env : apr_env }

  val to_aexpr : t -> Texpr1.t

  val cst : apr_env -> Coeff.t -> t
  val var : apr_env -> mvar -> t
  val unop : unop -> t -> t
  val binop : binop -> t -> t -> t

  val get_var_mexpr : mexpr -> mvar list

  val get_env : t -> Environment.t

  val extend_environment : t -> apr_env -> t

  val weak_cp : mvar -> int -> mvar
  val weak_transf : int Mm.t -> mexpr -> int Mm.t * mexpr

  val print : Format.formatter -> t -> unit
end = struct
  type unop = Texpr0.unop
  type binop = Texpr0.binop
  type typ = Apron.Texpr0.typ
  type round = Apron.Texpr0.round

  type mexpr =
    | Mcst of Coeff.t
    | Mvar of mvar
    | Munop of unop * mexpr * typ * round
    | Mbinop of binop * mexpr * mexpr * typ * round

  type t = { mexpr : mexpr;
             env : apr_env }

  let rec e_aux = function
    | Mcst c -> Texpr1.Cst c
    | Mvar mvar -> Texpr1.Var (avar_of_mvar mvar)
    | Munop (op1, a, t, r) -> Texpr1.Unop (op1, e_aux a, t, r)
    | Mbinop (op2, a, b, t, r) -> Texpr1.Binop (op2, e_aux a, e_aux b, t, r)

  let to_aexpr t = Texpr1.of_expr t.env (e_aux t.mexpr)

  let cst env c = { mexpr = Mcst c; env = env }

  let var env v = { mexpr = Mvar v; env = env }

  let unop op1 a = { a with
                     mexpr = Munop (op1, a.mexpr, Texpr1.Int, round_typ) }

  let binop op2 a b =
    if not (Environment.equal a.env b.env) then
      raise (Aint_error "Environment mismatch")
    else { mexpr = Mbinop (op2, a.mexpr, b.mexpr, Texpr1.Int, round_typ);
           env = a.env }

  let weak_cp v i = Temp ("wcp_" ^ string_of_mvar v, i, ty_mvar v)

  (* We rewrite the expression to perform soundly weak updates *)
  let rec weak_transf map e =
    match e with
    | Mcst c -> (map, Mcst c)
    | Mvar mvar ->
      if weak_update mvar then
        let i = Mm.find_default 0 mvar map in
        let map' = Mm.add mvar (i + 1) map in
        (map', Mvar (weak_cp mvar i))
      else (map, Mvar mvar)

    | Munop (op1, a, t, r) ->
      let map',a' = weak_transf map a in
      (map', Munop (op1, a', t, r))

    | Mbinop (op2, a, b, t, r) ->
      let map',a' = weak_transf map a in
      let map'',b' = weak_transf map' b in
      (map'', Mbinop (op2, a', b', t, r))

  let get_var_mexpr e =
    let rec aux acc = function
    | Mcst _ -> acc
    | Mvar mvar -> mvar :: acc
    | Munop (_, a, _, _) -> aux acc a
    | Mbinop (_, a, b, _, _) -> aux (aux acc a) b in
    aux [] e |> List.sort_uniq Pervasives.compare

  let get_env a = a.env

  let extend_environment t apr_env =
    let cmp = Environment.compare t.env apr_env in
    if cmp = -1 || cmp = 0 then
      { t with env = apr_env }
    else begin
      Format.eprintf "@[%a@;%a@]@." pp_apr_env t.env pp_apr_env apr_env;
      raise (Failure "The environment is not compatible") end

  let print ppf t = to_aexpr t |> Texpr1.print ppf
end


(******************)
(* Tcons1 Wrapper *)
(******************)

module Mtcons : sig
  type t
  type typ = Apron.Lincons0.typ

  val make : Mtexpr.t -> typ -> t

  val to_atcons : t -> Tcons1.t

  val get_expr : t -> Mtexpr.t
  val get_typ : t -> typ
  val get_env : t -> apr_env

  val print : Format.formatter -> t -> unit
end = struct
  type typ = Apron.Lincons0.typ

  type t = { expr : Mtexpr.t;
             typ : typ }

  let make t ty = { expr = t; typ = ty }

  let to_atcons t = Tcons1.make (Mtexpr.to_aexpr t.expr) t.typ

  let get_expr t = t.expr
  let get_typ t = t.typ
  let get_env t = Mtexpr.get_env t.expr

  let print ppf t = to_atcons t |> Tcons1.print ppf
end


(*************)
(* Mpq Utils *)
(*************)

(* Return 2^n *)
let mpq_pow n =
  let cast_div = Mpq.of_int 1 in
  let mpq2 = Mpq.of_int 1 in
  Mpq.mul_2exp cast_div mpq2 n;
  cast_div

(* Return 2^n - y *)
let mpq_pow_minus n y =
  Mpqf.sub (mpq_pow n |> Mpqf.of_mpq) (Mpqf.of_int y)

let cst_of_mpqf apr_env n =
  Mtexpr.cst apr_env (Coeff.s_of_mpqf n)

(* Return the texpr 2^n - y *)
let cst_pow_minus apr_env n y =
  let cast_div = mpq_pow_minus n y in
  cst_of_mpqf apr_env cast_div


(*******************)
(* Abstract Values *)
(*******************)

module type AprManager = sig
  type t

  val man : t Apron.Manager.t
end

module BoxManager : AprManager = struct
  type t = Box.t

  let man = Box.manager_alloc ()
end

module OctManager : AprManager = struct
  type t = Oct.t

  let man = Oct.manager_alloc ()
end

module PplManager : AprManager = struct
  type t = Ppl.strict Ppl.t

  let man = Ppl.manager_alloc_strict ()
end

module type AbsNumType = sig
  type t

  (* Make a top value defined on the given variables *)
  val make : mvar list -> t

  val meet : t -> t -> t
  val meet_list : t list -> t

  val join : t -> t -> t
  val join_list : t list -> t

  val widening : t -> t -> t

  val forget_list : t -> mvar list -> t

  val is_included : t -> t -> bool
  val is_bottom : t -> bool
  val bottom : t -> t

  val expand : t -> mvar -> mvar list -> t
  val fold : t -> mvar list -> t

  val bound_variable : t -> mvar -> Interval.t
  val bound_texpr : t -> Mtexpr.t -> Interval.t

  val assign_expr : ?force:bool -> t -> mvar -> Mtexpr.t -> t

  val meet_constr : t -> Mtcons.t -> t

  (* Unify the two abstract values on their least common environment. *)
  val unify : t -> t -> t

  (* Variables that are removed are first existentially quantified, and
     variables that are introduced are unconstrained. *)
  val change_environment : t -> mvar list -> t

  val get_env : t -> Environment.t

  val print : ?full:bool -> Format.formatter -> t -> unit
end


module AbsNumImpl (Manager : AprManager) : AbsNumType = struct

  type t = Manager.t Abstract1.t
  let man = Manager.man

  let make l =
    let vars = List.map avar_of_mvar l |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in
    let env = Environment.make vars empty_var_array in
    Abstract1.top man env

  let lce a a' =
    let lce = Environment.lce (Abstract1.env a) (Abstract1.env a') in
    (Abstract1.change_environment man a lce false,
     Abstract1.change_environment man a' lce false)

  let lce_list l =
    if l = [] then raise (Aint_error "Lce of an empty list");
    let i_env = Abstract1.env (List.hd l) in
    let lce = List.fold_left (fun e_acc x ->
        Environment.lce e_acc (Abstract1.env x))
        i_env l in
    List.map (fun a -> Abstract1.change_environment man a lce false) l

  let meet a a' =
    let a,a' = lce a a' in
    Abstract1.meet man a a'

  let meet_list a_list =
    if a_list = [] then raise (Aint_error "Meet of an empty list");
    let a_list = lce_list a_list in
    Abstract1.meet_array man (Array.of_list a_list)

  let join a a' =
    let a,a' = lce a a' in
    Abstract1.join man a a'

  let join_list a_list =
    if a_list = [] then raise (Aint_error "Join of an empty list");
    let a_list = lce_list a_list in
    Abstract1.join_array man (Array.of_list a_list)

  let int_thresholds =
    (* For unsigned *)
    List.map (fun i -> mpq_pow_minus i 1) [8;16;32;128;256]
    (* For signed *)
    @ List.map (fun i -> mpq_pow_minus i 1) [7;15;31;127;255]
    @ List.map (fun i -> mpq_pow_minus i 0) [7;15;31;127;255]

  let neg i = Mpqf.neg i

  let lcons env v i vneg iminus =
    let e = Linexpr1.make env in
    let ci = Coeff.s_of_mpqf (if iminus then neg i else i)
    and cv = Coeff.s_of_int (if vneg then -1 else 1) in
    let () = Linexpr1.set_list e [cv,v] (Some ci) in
    e

  let thresholds env =
    let arr_vars,_ = Environment.vars env in
    let vars = Array.to_list arr_vars in
    let cons = List.fold_left (fun acc v ->
        List.fold_left (fun acc i ->
            let lc = lcons env v i in
            (Lincons1.make (lc true true) Lincons0.SUPEQ)
            :: (Lincons1.make (lc true false) Lincons0.SUPEQ)
            :: (Lincons1.make (lc false true) Lincons0.SUPEQ)
            :: (Lincons1.make (lc false false) Lincons0.SUPEQ)
            :: acc) acc int_thresholds)
        [] vars in
    let arr = Lincons1.array_make env (List.length cons) in
    let () = List.iteri (fun i c -> Lincons1.array_set arr i c) cons in
    arr

  (* let widening a a' =
   *   let a,a' = lce a a' in
   *   let thrs = thresholds (Abstract1.env a) in
   *   (\* Be careful to join a and a' before calling widening. Some abstract domain,
   *      e.g. Polka, seem to assume that a is included in a'
   *      (and may segfault otherwise!). *\)
   *   Abstract1.widening_threshold man a a' thrs *)

  let widening a a' =
    let a,a' = lce a a' in
    (* Be careful to join a and a' before calling widening. Some abstract domain,
       e.g. Polka, seem to assume that a is included in a'
       (and may segfault otherwise!). *)
    Abstract1.widening man a a'

  let forget_list a l =
    let env = Abstract1.env a in
    let al = List.filter
        (Environment.mem_var env) (List.map avar_of_mvar l) in
    Abstract1.forget_array man a (Array.of_list al) false

  let is_included a a' =
    let a,a' = lce a a' in
    Abstract1.is_leq man a a'

  let is_bottom a = Abstract1.is_bottom man a

  let bottom a = Abstract1.bottom man (Abstract1.env a)

  let expand a v v_list =
    let v_array = Array.of_list (List.map avar_of_mvar v_list) in
    Abstract1.expand man a (avar_of_mvar v) v_array

  let fold a v_list =
    let v_array = Array.of_list (List.map avar_of_mvar v_list) in
    Abstract1.fold man a v_array

  let bound_variable t v = Abstract1.bound_variable man t (avar_of_mvar v)

  let add_weak_cp a map =
    Mm.fold (fun v i a ->
        let vs = List.init i (Mtexpr.weak_cp v) in
        expand a v vs) map a

  let rem_weak_cp a map =
    Mm.fold (fun v i a ->
        let vs = List.init i (Mtexpr.weak_cp v) in
        fold a (v :: vs)) map a

  let prepare_env env mexpr =
    let vars_mexpr =
      List.map avar_of_mvar (Mtexpr.get_var_mexpr mexpr) |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in
    let env_mexpr = Environment.make vars_mexpr empty_var_array in
    Environment.lce env env_mexpr

  let bound_texpr a (e : Mtexpr.t) =
    (* We use a different variable for each occurrence of weak variables *)
    let map,mexpr = Mtexpr.weak_transf Mm.empty e.mexpr in
    let a = add_weak_cp a map in

    let env = prepare_env (Abstract1.env a) e.mexpr in

    let a = Abstract1.change_environment man a env false in

    (* We prepare the expression *)
    let e' = Mtexpr.to_aexpr { Mtexpr.mexpr = mexpr;
                               Mtexpr.env = env } in

    (* We bound the expression *)
    Abstract1.bound_texpr man a e'

  let env_add_mvar env v =
    let add_single v env =
      let av = avar_of_mvar v in
      if Environment.mem_var env av then env
      else
        Environment.add env
          (Array.of_list [av])
          (Array.make 0 (Var.of_string "")) in

    match v with
    | Mvalue (Avar at) | MvarOffset at ->
      add_single (Mvalue (Avar at)) env
      |> add_single (MvarOffset at)
    | _ -> add_single v env

  (* If force is true then we do a forced strong update on v. *)
  let assign_expr ?force:(force=false) a v (e : Mtexpr.t) =
    (* We use a different variable for each occurrence of weak variables *)
    let map,mexpr = Mtexpr.weak_transf Mm.empty e.mexpr in
    let a = add_weak_cp a map in
    (* We do the same for the variable receiving the assignment *)
    let v_weak = weak_update v && not force in
    let a,v_cp = if v_weak then
        let v_cp = Temp ("weaklv_" ^ string_of_mvar v,0, ty_mvar v) in
        (expand a v [v_cp], v_cp)
      else (a, v) in

    (* If v is not in the environment, we add it *)
    let env = env_add_mvar (Abstract1.env a) v_cp in

    (* We add the variables in mexpr to the environment *)
    let env = prepare_env env mexpr in

    let a = Abstract1.change_environment man a env false in

    (* We prepare the expression *)
    let e' = Mtexpr.to_aexpr { Mtexpr.mexpr = mexpr;
                               Mtexpr.env = env } in

    (* We evaluate the expression *)
    let a = Abstract1.assign_texpr man a (avar_of_mvar v_cp) e' None in

    (* We fold back the added variables *)
    let a = rem_weak_cp a map in
    if v_weak then fold a [v; v_cp] else a


  let print : ?full:bool -> Format.formatter -> t -> unit =
    fun ?full:(full=false) fmt a ->
      if full && (Ppl.manager_is_ppl man) then
        Format.fprintf fmt "@[%a@]@;" Abstract1.print a;
      let apr_env = Abstract1.env a in
      let (arr_vars, _) = Environment.vars apr_env in
      let vars = Array.to_list arr_vars in

      let rec pp_abs fmt l = match l with
        | [] -> Format.fprintf fmt ""
        | v :: t ->
          if not (Abstract1.is_variable_unconstrained man a v)
          && not (variables_ignore v) then
            let vi = Abstract1.bound_variable man a v in
            Format.fprintf fmt "@[%s: %a@]%a%a"
              (Var.to_string v)
              Interval.print vi
              (fun fmt () -> if t = [] then () else Format.fprintf fmt "@;") ()
              pp_abs t
          else pp_abs fmt t in

      Format.fprintf fmt "@[<v 0>%a@]" pp_abs vars

  let meet_constr a c =
    let e = Mtcons.get_expr c in
    (* We use a different variable for each occurrence of weak variables *)
    let map,mexpr = Mtexpr.weak_transf Mm.empty e.mexpr in
    let a = add_weak_cp a map in

    (* We prepare the expression *)
    let e = Mtexpr.to_aexpr { Mtexpr.mexpr = mexpr;
                               Mtexpr.env = Abstract1.env a } in
    let c = Tcons1.make e (Mtcons.get_typ c) in

    (* We evaluate the constraint *)
    let c_array = Tcons1.array_make (Tcons1.get_env c) 1 in
    Tcons1.array_set c_array 0 c;
    let a = Abstract1.meet_tcons_array man a c_array in

    (* We fold back the added variables *)
    rem_weak_cp a map

  let unify a a' = Abstract1.unify man a a'

  let change_environment a mvars =
    let env_vars = List.map avar_of_mvar mvars |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in
    let new_env = Environment.make env_vars empty_var_array in
    Abstract1.change_environment man a new_env false

  let get_env a = Abstract1.env a

end


(*******************)
(* Domains Product *)
(*******************)


type v_dom = Nrd of int | Ppl of int

let string_of_dom = function
  | Nrd i -> "Nrd" ^ string_of_int i
  | Ppl i -> "Ppl" ^ string_of_int i

module Mdom = Map.Make(struct
    type t = v_dom

    let compare = Pervasives.compare
    let equal u v = u = v
  end)

let is_prefix u v =
  if String.length u <= String.length v then
    String.sub v 0 (String.length u) = u
  else false

module AbsNumProd (NonRel : AbsNumType) (PplDom : AbsNumType)
  : AbsNumType = struct

  type t = { nrd : NonRel.t Mdom.t;
             ppl : PplDom.t Mdom.t }

  (* For now we fixed the domains, and we use only two of them, one non-relational
     and on Ppl. Still, we generalized to n different domains whenever possible
     to help future possible extentions. *)
  let vdom = function
    | Temp _ | WTemp _ -> assert false

    (* (\* REM *\)
     * | Mvalue (Avar v) | MvarOffset v ->
     *   let xs = ["u";"tmp"; "mul"] in
     *   if List.exists (fun x -> is_prefix x v.v_name) xs then
     *     Nrd 0
     *   else Ppl 0 *)

    | Mvalue (Avar _) | MvarOffset _ -> Ppl 0

    | Mglobal _
    | MinValue _
    | MmemRange _ -> Ppl 0

    | Mvalue (AarrayEl _)
    | Mvalue (Aarray _) -> Nrd 0

  let nrddoms = [Nrd 0]
  let ppldoms = [Ppl 0]

  let split_doms l =
    let rec aux (ores,pres) = function
      | [] -> (ores, pres)
      | v :: tail ->
        let res' = match vdom v with
          | Ppl _ as d ->
            if List.mem_assoc d pres then
              (ores, assoc_up d (fun x -> v :: x) pres)
            else
              (ores, (d,[v]) :: pres)

          | Nrd _ as d ->
            if List.mem_assoc d pres then
              (assoc_up d (fun x -> v :: x) ores, pres)
            else
              ((d,[v]) :: ores, pres) in

        aux res' tail in

    aux (List.map (fun d -> (d,[])) nrddoms,
         List.map (fun d -> (d,[])) ppldoms) l

  let make l =
    let (ores,pres) = split_doms l in
    let a = { nrd = Mdom.empty; ppl = Mdom.empty } in

    let a = List.fold_left (fun a (d,lvs) ->
        { a with nrd = Mdom.add d (NonRel.make lvs) a.nrd })
      a ores in

    List.fold_left (fun a (d,lvs) ->
        { a with ppl = Mdom.add d (PplDom.make lvs) a.ppl })
      a pres

  let un_app fnrd fppl a =
    { nrd = Mdom.mapi fnrd a.nrd;
      ppl = Mdom.mapi fppl a.ppl }

  let bin_app fnrd fppl a a' =
    let f_opt f k u v = match u,v with
      | None, _ | _, None ->
        let s = Printf.sprintf
            "bin_app: Domain %s does not exist" (string_of_dom k) in
        raise (Failure s)
      | Some x, Some y -> Some (f x y) in

    { nrd = Mdom.merge (f_opt fnrd) a.nrd a'.nrd;
      ppl = Mdom.merge (f_opt fppl) a.ppl a'.ppl }

  let list_app fnrd fppl (l : t list) =
    match l with
    | [] -> raise (Aint_error "list_app of an empty list");
    | a :: _ ->

      { nrd = Mdom.mapi (fun k _ ->
            let els = List.map (fun x -> Mdom.find k x.nrd) l in
            fnrd els) a.nrd;
        ppl = Mdom.mapi (fun k _ ->
            let els = List.map (fun x -> Mdom.find k x.ppl) l in
            fppl els) a.ppl}

  let meet = bin_app NonRel.meet PplDom.meet

  let meet_list = list_app NonRel.meet_list PplDom.meet_list

  let join = bin_app NonRel.join PplDom.join

  let join_list = list_app NonRel.join_list PplDom.join_list

  let widening = bin_app NonRel.widening PplDom.widening

  let forget_list a l =
    let f1 _ x = NonRel.forget_list x l
    and f2 _ x = PplDom.forget_list x l in
    un_app f1 f2 a

  let is_included a a' =
    (Mdom.for_all (fun d t -> NonRel.is_included t (Mdom.find d a'.nrd)) a.nrd)
    &&
    (Mdom.for_all (fun d t -> PplDom.is_included t (Mdom.find d a'.ppl)) a.ppl)


  let is_bottom a =
    (Mdom.for_all (fun _ t -> NonRel.is_bottom t) a.nrd)
    && (Mdom.for_all (fun _ t -> PplDom.is_bottom t) a.ppl)

  let bottom a =
    let f1 _ x = NonRel.bottom x
    and f2 _ x = PplDom.bottom x in
    un_app f1 f2 a

  let expand a v v_list =
    let f1 d x = if vdom v = d then NonRel.expand x v v_list else x
    and f2 d x = if vdom v = d then PplDom.expand x v v_list else x in
    un_app f1 f2 a

  let fold a v_list = match v_list with
    | [] -> raise (Aint_error "list_app of an empty list")
    | v :: _ ->
      let f1 d x = if vdom v = d then NonRel.expand x v v_list else x
      and f2 d x = if vdom v = d then PplDom.expand x v v_list else x in
      un_app f1 f2 a

  let bound_variable a v = match vdom v with
    | Nrd _ -> NonRel.bound_variable (Mdom.find (vdom v) a.nrd) v
    | Ppl _ -> PplDom.bound_variable (Mdom.find (vdom v) a.ppl) v

  let expr_doms e =
    let rec aux acc = function
    | Mtexpr.Mcst _ -> acc
    | Mtexpr.Mvar v ->
      if List.mem (vdom v) acc then acc else (vdom v) :: acc
    | Mtexpr.Munop (_, e1, _, _) -> aux acc e1
    | Mtexpr.Mbinop (_, e1, e2, _, _) -> aux (aux acc e1) e2 in

    aux [] e

  (* Replace all variables not in domain d by an interval *)
  let proj_expr a d (e : Mtexpr.t) =
    let env = e.env in
    let m_make e = Mtexpr.({ mexpr = e; env = env }) in

    let rec proj_mexpr (e : Mtexpr.mexpr) = match expr_doms e with
      | [] -> m_make e
      | [d'] ->
        if d = d' then m_make e
        else
          let int = match d' with
          | Nrd _ -> NonRel.bound_texpr (Mdom.find d' a.nrd) (m_make e)
          | Ppl _ -> PplDom.bound_texpr (Mdom.find d' a.ppl) (m_make e) in
          Mtexpr.cst env (Coeff.Interval int)

      | _ -> match e with
        (* | Mtexpr.Mcst c -> Mtexpr.cst env c
         * | Mtexpr.Mvar v ->
         *   if vdom v = d then Mtexpr.var env v
         *   else Mtexpr.cst env (Coeff.Interval (bound_variable a v)) *)
        | Mtexpr.Munop (op, e1, _, _) -> Mtexpr.unop op (proj_mexpr e1)
        | Mtexpr.Mbinop (op, e1, e2, _, _) ->
          Mtexpr.binop op (proj_mexpr e1) (proj_mexpr e2)
        | _ -> assert false in

    proj_mexpr e.mexpr

  let proj_constr a d (c : Mtcons.t) =
    Mtcons.make (proj_expr a d (Mtcons.get_expr c)) (Mtcons.get_typ c)

  (* This works only if there is only one Ppl domain (Ppl 0). *)
  let bound_texpr a (e : Mtexpr.t) =
    let p_e = proj_expr a (Ppl 0) e in
    PplDom.bound_texpr (Mdom.find (Ppl 0) a.ppl) p_e

  (* If force is true then we do a forced strong update on v. *)
  let assign_expr ?force:(force=false) a v (e : Mtexpr.t) =
    let d = vdom v in
    let p_e = proj_expr a d e in
    match d with
    | Nrd _ ->
      let d_a = Mdom.find d a.nrd in
      let d_a' = NonRel.assign_expr ~force:force d_a v p_e in
      { a with nrd = Mdom.add d d_a' a.nrd }
    | Ppl _ ->
      let d_a = Mdom.find d a.ppl in
      let d_a' = PplDom.assign_expr ~force:force d_a v p_e in
      { a with ppl = Mdom.add d d_a' a.ppl }


  let meet_constr a c =
    let f1 d x = NonRel.meet_constr x (proj_constr a d c)
    and f2 d x = PplDom.meet_constr x (proj_constr a d c) in
    un_app f1 f2 a

  let unify = bin_app NonRel.unify PplDom.unify

  let change_environment a mvars =
    let (ores,pres) = split_doms mvars in

    let f1 d x = NonRel.change_environment x (List.assoc d ores)
    and f2 d x = PplDom.change_environment x (List.assoc d pres) in
    un_app f1 f2 a

  let print : ?full:bool -> Format.formatter -> t -> unit =
    fun ?full:(full=false) fmt a ->
      let pp_map pp_el fmt l =
        pp_list pp_el fmt (List.map snd (Mdom.bindings l)) in

      Format.fprintf fmt "@[<v 0>%a%a@]"
        (pp_map (NonRel.print ~full:full)) a.nrd
        (pp_map (PplDom.print ~full:full)) a.ppl

  let get_env a =
    let l =
      Mdom.fold (fun _ a l ->
          let vars,_ = NonRel.get_env a |> Environment.vars in
          Array.to_list vars @ l) a.nrd []
      |> Mdom.fold (fun _ a l ->
          let vars,_ = PplDom.get_env a |> Environment.vars in
          Array.to_list vars @ l) a.ppl in

    let env_vars = Array.of_list l
    and empty_var_array = Array.make 0 (Var.of_string "") in
    Environment.make env_vars empty_var_array
end


(***********************************)
(* Numerical Domain With Profiling *)
(***********************************)

module MakeAbsNumProf(A : AbsNumType) : AbsNumType = struct
  include A

  let () = Prof.record "make"
  let make x =
    let t = Sys.time () in
    let r = A.make x in
    let () = Prof.call "make" (Sys.time () -. t) in
    r

  let () = Prof.record "is_bottom"
  let is_bottom x =
    let t = Sys.time () in
    let r = A.is_bottom x in
    let () = Prof.call "is_bottom" (Sys.time () -. t) in
    r

  let () = Prof.record "bottom"
  let bottom x =
    let t = Sys.time () in
    let r = A.bottom x in
    let () = Prof.call "bottom" (Sys.time () -. t) in
    r

  let () = Prof.record "meet_list"
  let meet_list x =
    let t = Sys.time () in
    let r = A.meet_list x in
    let () = Prof.call "meet_list" (Sys.time () -. t) in
    r

  let () = Prof.record "join_list"
  let join_list x =
    let t = Sys.time () in
    let r = A.join_list x in
    let () = Prof.call "join_list" (Sys.time () -. t) in
    r

  let () = Prof.record "meet"
  let meet x y =
    let t = Sys.time () in
    let r = A.meet x y in
    let () = Prof.call "meet" (Sys.time () -. t) in
    r

  let () = Prof.record "join"
  let join x y =
    let t = Sys.time () in
    let r = A.join x y in
    let () = Prof.call "join" (Sys.time () -. t) in
    r

  let () = Prof.record "widening"
  let widening x y =
    let t = Sys.time () in
    let r = A.widening x y in
    let () = Prof.call "widening" (Sys.time () -. t) in
    r

  let () = Prof.record "is_included"
  let is_included x y =
    let t = Sys.time () in
    let r = A.is_included x y in
    let () = Prof.call "is_included" (Sys.time () -. t) in
    r

  let () = Prof.record "forget_list"
  let forget_list x y =
    let t = Sys.time () in
    let r = A.forget_list x y in
    let () = Prof.call "forget_list" (Sys.time () -. t) in
    r

  let () = Prof.record "fold"
  let fold x y =
    let t = Sys.time () in
    let r = A.fold x y in
    let () = Prof.call "fold" (Sys.time () -. t) in
    r

  let () = Prof.record "bound_variable"
  let bound_variable x y =
    let t = Sys.time () in
    let r = A.bound_variable x y in
    let () = Prof.call "bound_variable" (Sys.time () -. t) in
    r

  let () = Prof.record "bound_texpr"
  let bound_texpr x y =
    let t = Sys.time () in
    let r = A.bound_texpr x y in
    let () = Prof.call "bound_texpr" (Sys.time () -. t) in
    r

  let () = Prof.record "meet_constr"
  let meet_constr x y =
    let t = Sys.time () in
    let r = A.meet_constr x y in
    let () = Prof.call "meet_constr" (Sys.time () -. t) in
    r

  let () = Prof.record "unify"
  let unify x y =
    let t = Sys.time () in
    let r = A.unify x y in
    let () = Prof.call "unify" (Sys.time () -. t) in
    r

  let () = Prof.record "expand"
  let expand x y z =
    let t = Sys.time () in
    let r = A.expand x y z in
    let () = Prof.call "expand" (Sys.time () -. t) in
    r

  let () = Prof.record "assign_expr"
  let assign_expr ?force:(force=false) x y z =
    let t = Sys.time () in
    let r = A.assign_expr ~force:force x y z in
    let () = Prof.call "assign_expr" (Sys.time () -. t) in
    r
end

module AbsNum = MakeAbsNumProf(
    AbsNumProd (AbsNumImpl(BoxManager)) (AbsNumImpl(PplManager)))

(* module AbsNum = MakeAbsNumProf(
 *     AbsNumProd (AbsNumImpl(OctManager)) (AbsNumImpl(PplManager))) *)


(***************************************)
(* Boolean combination of constraints. *)
(***************************************)

type btcons =
  | BLeaf of Mtcons.t
  | BVar of string * bool
  | BAnd of btcons * btcons
  | BOr of btcons * btcons

let rec pp_btcons ppf = function
  | BLeaf t -> Mtcons.print ppf t

  | BVar (s,b) ->
    if b then Format.fprintf ppf "%s" s
    else Format.fprintf ppf "NOT %s" s

  | BAnd (bl,br) ->
    Format.fprintf ppf "(%a@ AND@ %a)"
      pp_btcons bl pp_btcons br

  | BOr (bl,br) ->
    Format.fprintf ppf "(%a@ OR@ %a)"
      pp_btcons bl pp_btcons br

let true_tcons1 env =
  let zero_t = Coeff.s_of_int 0 in
  Mtcons.make (Mtexpr.cst env zero_t) Tcons1.EQ

let false_tcons1 env =
  let zero_t = Coeff.s_of_int 0 in
  Mtcons.make (Mtexpr.cst env zero_t) Tcons1.DISEQ

let bvar_name v neg =
  if neg then "f_" ^ v else "t_" ^ v

(* Return the negation of c, except for EQMOD.
   For EQMOD, we return a constraint that always hold. *)
let flip_constr c =
  let t = Mtcons.get_expr c in
  match Mtcons.get_typ c with
  | Tcons1.EQ -> Mtcons.make t Tcons1.DISEQ |> some
  | Tcons1.DISEQ -> Mtcons.make t Tcons1.EQ |> some
  | Tcons1.SUPEQ ->
    let mt = Mtexpr.unop Texpr1.Neg t in
    Mtcons.make mt Tcons1.SUP |> some

  | Tcons1.SUP ->
    let mt = Mtexpr.unop Texpr1.Neg t in
    Mtcons.make mt Tcons1.SUPEQ |> some

  | Tcons1.EQMOD _ -> None (* Remark: For small i, we could do something *)


exception Bop_not_supported

let rec flip_btcons : btcons -> btcons option = fun c ->
  let rec flip_btcons_aux = function
    | BLeaf c -> begin match flip_constr c with
        | Some fc -> BLeaf fc
        | None -> raise Bop_not_supported end
    | BVar (s,bool) -> BVar (s, true <> bool)
    | BAnd (bl,br) -> BOr (flip_btcons_aux bl, flip_btcons_aux br)
    | BOr (bl,br) -> BAnd (flip_btcons_aux bl, flip_btcons_aux br) in

  try Some (flip_btcons_aux c) with Bop_not_supported -> None

module Scmp = struct
  type t = string
  let compare = compare
end

module Ms = Map.Make(Scmp)


(* Type of expression that have been split to remove IfThenElse *)
type s_expr = (btcons list * Mtexpr.t option) list

let sexpr_from_simple_expr : Mtexpr.t -> s_expr = fun expr ->
  [([], Some expr)]

let pp_s_expr fmt (e : s_expr) =
  let pp_el fmt (l,t_opt) =
    Format.fprintf fmt "@[<v 0>%d constraints:@;@[<v 1>%a@]@;term: @[%a@]@]"
      (List.length l)
      (pp_list pp_btcons) l
      (pp_opt Mtexpr.print) t_opt in

  Format.fprintf fmt "@[<v 0>%a@]"
    (pp_list pp_el) e


(*****************************)
(* Points-to Abstract Domain *)
(*****************************)

type pt_expr = | PtVars of mvar list | PtTop

module type PointsTo = sig
  type t

  (* make takes as input the set of memory locations of the program *)
  val make : mem_loc list -> t

  val meet : t -> t -> t
  val join : t -> t -> t

  val widening : t -> t -> t

  val forget_list : t -> mvar list -> t
  val is_included : t -> t -> bool

  val top_mem_loc : t -> mem_loc list

  val expand : t -> mvar -> mvar list -> t
  val fold : t -> mvar list -> t

  val var_points_to : t -> mvar -> mem_loc list
  val assign_pt_expr : t -> mvar -> pt_expr -> t

  val unify : t -> t -> t

  val print : Format.formatter -> t -> unit
end

module PointsToImpl : PointsTo = struct
  type t = { pts : mem_loc list Ms.t;
             top : mem_loc list }

  let make mls =
    let string_of_var v = match v.v_ty with
      | Arr _ -> assert false (* We should not have arrays as inputs
                                 to export functions. *)
      | Bty _ -> string_of_mvar (Mvalue (Avar v)) in

    let pts = List.fold_left (fun pts x -> match x with
        | MemLoc v -> Ms.add (string_of_var v) [x] pts)
        Ms.empty mls in
    { pts = pts ; top = mls }

  let meet : t -> t -> t = fun t t' ->
    let pts'' =
      Ms.merge (fun _ aop bop -> match aop,bop with
          | None, _ | _, None -> None
          | Some l, Some l' ->
            let l_inter = List.filter (fun x -> List.mem x l') l in
            Some (List.sort_uniq Pervasives.compare l_inter ))
        t.pts t'.pts in
    { t with pts = pts'' }

  let join : t -> t -> t = fun t t' ->
    let pts'' =
      Ms.merge (fun _ aop bop -> match aop,bop with
          | None, x | x, None -> x
          | Some l, Some l' ->
            Some (List.sort_uniq Pervasives.compare (l @ l')))
        t.pts t'.pts in
    { t with pts = pts'' }

  let widening t t' = join t t'

  let svar_points_to : t -> string -> mem_loc list = fun t s_var ->
    if Ms.mem s_var t.pts then Ms.find s_var t.pts else []

  let var_points_to : t -> mvar -> mem_loc list = fun t var ->
    let s_var = string_of_mvar var in
    svar_points_to t s_var

  let forget_list : t -> mvar list -> t = fun t l_rem ->
    let vl_rem = List.map string_of_mvar l_rem in
    { t with pts = Ms.filter (fun v _ -> not (List.mem v vl_rem)) t.pts }

  let is_included : t -> t -> bool = fun t t' ->
    Ms.for_all (fun v l ->
        let l' = svar_points_to t' v in
        List.for_all (fun x -> List.mem x l') l) t.pts

  let top_mem_loc : t -> mem_loc list = fun t -> t.top

  let assign_pt_expr : t -> mvar -> pt_expr -> t = fun t v e ->
    let v_pts = match e with
      | PtTop -> t.top
      | PtVars el ->
        List.fold_left (fun acc var ->
            var_points_to t var @ acc) [] el
        |> List.sort_uniq Pervasives.compare in
    { t with pts = Ms.add (string_of_mvar v) v_pts t.pts }

  let unify : t -> t -> t = meet

  let expand : t -> mvar -> mvar list -> t = fun t v l ->
    let v_pts = var_points_to t v in
    let pts' = List.fold_left (fun acc v' ->
        Ms.add (string_of_mvar v') v_pts acc) t.pts l in
    { t with pts = pts' }

  let fold : t -> mvar list -> t = fun t l -> match l with
    | [] -> assert false
    | v :: tail ->
      let t' = assign_pt_expr t v (PtVars l) in
      forget_list t' tail

  let pp_memlocs ppf l =
    pp_list (fun ppf x -> match x with
          MemLoc v -> Format.fprintf ppf "%s@," v.v_name)
      ppf l

  let print ppf t =
    Format.fprintf ppf "@[<v 0>%a@]"
      (pp_list (fun ppf (k,l) ->
           Format.fprintf ppf "@[<h>%s: %a@]@;"
             k pp_memlocs l))
      (Ms.bindings t.pts)

end


(************************************************)
(* Abstraction of numerical and boolean values. *)
(************************************************)

(* Extends a numerical domain to include boolean variable abstractions and
   keep track of initialized variables and points-to information *)
module type AbsNumBoolType = sig
  type t

  (* Make a top value defined on the given variables *)
  val make : mvar list -> mem_loc list -> t

  val meet : t -> t -> t
  val join : t -> t -> t
  val widening : t -> t -> t

  val forget_list : t -> mvar list -> t
  val forget_bvar : t -> string -> t

  val is_included : t -> t -> bool
  val is_bottom : t -> bool

  val top_mem_loc : t -> mem_loc list

  val expand : t -> mvar -> mvar list -> t
  val fold : t -> mvar list -> t

  val bound_variable : t -> mvar -> Interval.t
  val bound_texpr : t -> Mtexpr.t -> Interval.t

  (* Does not change the points-to information *)
  val assign_sexpr : ?force:bool -> t -> mvar -> s_expr -> t
  val assign_bexpr : t -> string -> btcons -> t

  val var_points_to : t -> mvar -> mem_loc list
  val assign_pt_expr : t -> mvar -> pt_expr -> t

  val meet_btcons : t -> btcons -> t

  (* Unify the two abstract values on their least common environment. *)
  val unify : t -> t -> t

  (* Variables that are removed are first existentially quantified, and
     variables that are introduced are unconstrained. *)
  val change_environment : t -> mvar list -> t

  val clear_init : t -> atype list -> t
  val is_init : t -> atype -> t
  val check_init : t -> atype -> bool

  val get_env : t -> Environment.t

  val print : ?full:bool -> Format.formatter -> t -> unit
end


module AbsBoolNoRel (AbsNum : AbsNumType) (Pt : PointsTo)
  : AbsNumBoolType = struct

  (* Ms.find s init is an over-approx of the program state where s
     is *not* initialized.
     Remark: we lazily populate init *)
  type t = { bool : AbsNum.t Ms.t;
             init : AbsNum.t Ms.t;
             num : AbsNum.t;
             points_to : Pt.t }

  let map2 : ('a -> 'b -> 'c) -> 'a Ms.t -> 'b Ms.t -> 'c Ms.t =
    fun f map_a map_b ->
      Ms.mapi (fun k a ->
          let b = Ms.find k map_b in
          f a b)
        map_a

  let merge_init_dom t t' =
    let eb = Ms.merge (fun _ x _ -> match x with
        | None -> Some t.num
        | Some _ -> x) t.init t'.init
    and eb' = Ms.merge (fun _ x _ -> match x with
        | None -> Some t'.num
        | Some _ -> x) t'.init t.init in
    ({ t with init = eb }, { t' with init = eb' })

  let apply f fpt t = { bool = Ms.map f t.bool;
                        init = Ms.map f t.init;
                        num = f t.num;
                        points_to = fpt t.points_to }

  (* Since init is lazily populated, we merge the domains before applying f *)
  let apply2 f fpt t t' =
    let t, t' = merge_init_dom t t' in
    { bool = map2 f t.bool t'.bool;
      init = map2 f t.init t'.init;
      num = f t.num t'.num;
      points_to = fpt t.points_to t'.points_to }

  let for_all2 : ('a -> 'b -> 'c) -> 'a Ms.t -> 'b Ms.t -> bool =
    fun f map_a map_b ->
      Ms.for_all (fun k a ->
          let b = Ms.find k map_b in
          f a b)
        map_a

  let rec bool_vars = function
    | [] -> []
    | h :: t ->
      if ty_mvar h = Bty Bool then
        let vh = string_of_mvar h in
        (bvar_name vh true) :: (bvar_name vh false) :: bool_vars t
      else bool_vars t

  let rec init_vars = function
    | [] -> []
    | Mvalue at :: t -> string_of_mvar (Mvalue at) :: init_vars t
    | _ :: t -> init_vars t

  let make : mvar list -> mem_loc list -> t = fun l mls ->
    let b_vars = bool_vars l in
    let abs = AbsNum.make l in
    let bmap = List.fold_left (fun bmap bv ->
        Ms.add bv abs bmap) Ms.empty b_vars in
    { bool = bmap;
      init = Ms.empty;
      num = abs;
      points_to = Pt.make mls }

  let unify_map : AbsNum.t Ms.t -> AbsNum.t Ms.t -> AbsNum.t Ms.t = fun b b' ->
    let eb = Ms.merge (fun _ x y -> match x with
        | None -> y
        | Some _ -> x) b b'
    and eb' = Ms.merge (fun _ x y -> match x with
        | None -> y
        | Some _ -> x) b' b in
    map2 AbsNum.unify eb eb'

  let meet : t -> t -> t = fun t t' ->
    { bool = map2 AbsNum.meet t.bool t'.bool;
      init = unify_map t.init t'.init;
      num = AbsNum.meet t.num t'.num;
      points_to = Pt.meet t.points_to t'.points_to }

  let join : t -> t -> t = apply2 AbsNum.join Pt.join

  let widening : t -> t -> t = apply2 AbsNum.widening Pt.widening

  let forget_list : t -> mvar list -> t = fun t l ->
    let f x = AbsNum.forget_list x l
    and f_pts x = Pt.forget_list x l in
    apply f f_pts t

  let forget_bvar : t -> string -> t  = fun t s ->
    { t with bool = Ms.add s t.num t.bool }

  (* No need to check anything on t.init and t'.init. *)
  let is_included : t -> t -> bool = fun t t' ->
    (AbsNum.is_included t.num t'.num)
    && (for_all2 AbsNum.is_included t.bool t'.bool)
    && (Pt.is_included t.points_to t'.points_to)

  let top_mem_loc : t -> mem_loc list = fun t -> Pt.top_mem_loc t.points_to

  let is_bottom : t -> bool = fun t -> AbsNum.is_bottom t.num

  let bound_variable : t -> mvar -> Interval.t = fun t v ->
    AbsNum.bound_variable t.num v

  let bound_texpr : t -> Mtexpr.t -> Interval.t = fun t e ->
    AbsNum.bound_texpr t.num e

  let expand : t -> mvar -> mvar list -> t = fun t v vl ->
    let f x = AbsNum.expand x v vl in
    let f_pts x = Pt.expand x v vl in
    apply f f_pts t

  let fold : t -> mvar list -> t = fun t vl ->
    let f x = AbsNum.fold x vl in
    let f_pts x = Pt.fold x vl in
    apply f f_pts t

  (* abs_beval t bexpr : evaluate bexpr in t.
     We split disequalities in two cases to improve precision. *)
  let rec abs_eval_btcons : t -> btcons -> AbsNum.t = fun t bexpr ->
    match bexpr with
    | BLeaf c -> begin match Mtcons.get_typ c with
        | Tcons0.DISEQ ->
          let bexpr_pos = BLeaf (Mtcons.make (Mtcons.get_expr c) Tcons0.SUP) in

          let minus_expr = Mtexpr.unop Texpr0.Neg (Mtcons.get_expr c) in
          let bexpr_neg = BLeaf (Mtcons.make minus_expr Tcons0.SUP) in

          abs_eval_btcons t (BOr (bexpr_pos,bexpr_neg))
        | _ -> AbsNum.meet_constr t.num c end

    | BVar (v,neg) -> Ms.find_default t.num (bvar_name v neg) t.bool

    | BOr (l_bexpr, r_bexpr) ->
      AbsNum.join
        (abs_eval_btcons t l_bexpr)
        (abs_eval_btcons t r_bexpr)

    | BAnd (l_bexpr, r_bexpr) ->
      AbsNum.meet
        (abs_eval_btcons t l_bexpr)
        (abs_eval_btcons t r_bexpr)

  let abs_eval_neg_btcons t bexpr = match flip_btcons bexpr with
    | None -> t.num
    | Some c -> abs_eval_btcons t c

  (* Assign an expression given by a list of constrained expression.
     We do not touch init and points_to there, this has to be done by manualy
     by the caller.
     We unpopulate init to be faster. This is sound if the evaluation of an
     expression neither modifies init not depend on it. *)
  let assign_sexpr : ?force:bool -> t -> mvar -> s_expr -> t =
    fun ?force:(force=false) t v s_expr ->

      let s_init = t.init in
      let points_to_init = t.points_to in
      let t = { t with init = Ms.empty } in

      (* We add temporary variables *)
      let n_env = AbsNum.get_env t.num in
      let constr_expr_list =
        List.map (fun (bexpr_list, expr) ->
            match bexpr_list with
            | [] -> (None,expr)
            | _ ->
              let constr = List.map (abs_eval_btcons t) bexpr_list
                           |> AbsNum.meet_list  in
              (Some constr,expr))
          s_expr in

      let t_list =
        List.map (fun (constr,expr) -> match expr with
            | Some e ->
              let e = Mtexpr.extend_environment e n_env in
              let t' = match constr with
                | None -> t
                | Some c -> apply (AbsNum.meet c) (fun x -> x) t in
              apply
                (fun x -> AbsNum.assign_expr ~force:force x v e)
                (fun x -> x) t'

            | None -> match constr with
              | None -> t
              | Some c -> apply (AbsNum.meet c) (fun x -> x) t)
          constr_expr_list in

      (* We compute the join of all the assignments *)
      let join_map b_list = match b_list with
        | [] -> assert false
        | h :: l ->
          Ms.mapi (fun key x ->
              let elems = x :: List.map (Ms.find key) l in
              AbsNum.join_list elems) h in

      let b_list,n_list = List.map (fun x -> x.bool) t_list,
                          List.map (fun x -> x.num) t_list in
      { bool = join_map b_list;
        init = s_init;
        num = AbsNum.join_list n_list;
        points_to = points_to_init }


  (* Assign a boolean expression.
     As we did in assign_sexpr, we unpopulate init *)
  let assign_bexpr t vb bexpr =
    let s_init = t.init in
    let points_to_init = t.points_to in

    let t = { t with init = Ms.empty } in

    let t_vb, f_vb = bvar_name vb true,
                     bvar_name vb false in

    let new_b = Ms.add t_vb (abs_eval_btcons t bexpr) t.bool
                |> Ms.add f_vb (abs_eval_neg_btcons t bexpr) in
    { bool = new_b;
      init = s_init;
      num = t.num;
      points_to = points_to_init }

  let var_points_to t v = Pt.var_points_to t.points_to v

  let assign_pt_expr t v pt_e =
    { t with points_to = Pt.assign_pt_expr t.points_to v pt_e }

  let meet_btcons : t -> btcons -> t = fun t c ->
    let cn = abs_eval_btcons t c in

    apply (AbsNum.meet cn) (fun x -> x) t

  let unify : t -> t -> t = fun t t' ->
    { bool = unify_map t.bool t'.bool;
      init = unify_map t.init t'.init;
      num = AbsNum.unify t.num t'.num;
      points_to = Pt.unify t.points_to t'.points_to }

  let change_environment : t -> mvar list -> t = fun t l ->
    let bvars = bool_vars l
    and ivars = init_vars l in
    (* We remove the variables that are not in l *)
    let b = Ms.filter (fun s _ -> List.mem s bvars) t.bool
    and init = Ms.filter (fun s _ -> List.mem s ivars) t.init in

    (* We add the variables that are in l but not in t.bool's domain.
       We do not need to do it for t.init, since it is lazily populated *)
    let b = List.fold_left (fun b s ->
        if Ms.mem s b then b else Ms.add s t.num b) b bvars in

    (* We change the environment of the underlying numerical domain *)
    let f x = AbsNum.change_environment x l in
    apply f (fun x -> x) { t with bool = b; init = init }

  let blast_if_array at = match at with
    | Aarray v ->
      let vi i = Mvalue (AarrayEl (v,i)) |> string_of_mvar in
      List.init (arr_range v) vi
    | _ -> [string_of_mvar (Mvalue at)]

  let clear_init : t -> atype list -> t = fun t l ->
    let l_ext = List.flatten (List.map blast_if_array l)  in
    let init = List.fold_left (fun init v -> Ms.remove v init) t.init l_ext in
    { t with init = init }

  let is_init : t -> atype -> t = fun t at ->
    let vats = blast_if_array at in
    let add_el init x = Ms.add x (AbsNum.bottom t.num) init in
    { t with init = List.fold_left add_el t.init vats }

  let check_init : t -> atype -> bool = fun t at ->
    let vats = blast_if_array at in
    let check x =
      let abs = try AbsNum.meet t.num (Ms.find x t.init) with
        | Not_found -> t.num in
      AbsNum.is_bottom abs in
    List.for_all check vats

  let get_env : t -> Environment.t = fun t -> AbsNum.get_env t.num

  let print : ?full:bool -> Format.formatter -> t -> unit =
    fun ?full:(full=false) fmt t ->
      AbsNum.print ~full:full fmt t.num
end


module AbsDom = AbsBoolNoRel (AbsNum) (PointsToImpl)


(**********************)
(* Typing Environment *)
(**********************)

module Ss = Set.Make(Scmp)

module Tcmp = struct
  type t = ty
  let compare = compare
end

module Mty = Map.Make (Tcmp)

type s_env = { s_glob : (string * Type.stype) Ms.t;
               m_locs : mem_loc list }

let pp_s_env fmt env =
  Format.printf fmt "@[<v>global variables:@;%a@]"
    (pp_list (fun fmt (_,(x,sw)) ->
         Format.fprintf fmt "@[%s: %a@]@,"
           x Printer.pp_ty (Conv.ty_of_cty sw)))
    (Ms.bindings env.s_glob)
    (pp_list (fun fmt i -> Format.fprintf fmt "%d" i))

let add_glob env x ws =
  let ty = Bty (U ws) in
  { env with s_glob = Ms.add x (x,Conv.cty_of_ty ty) env.s_glob }


let add_glob_var s v =
  let uv = L.unloc v in
  match uv.v_kind, uv.v_ty with
  | Global, Bty (U _) -> Ms.add uv.v_name (uv.v_name, Conv.cty_of_ty uv.v_ty) s
  | _ -> s

let rec add_glob_expr s = function
  | Pconst _ | Pbool _ | Parr_init _ -> s
  | Pglobal (sw,x) ->
    let ty = Bty (U sw) in
    Ms.add x (x,Conv.cty_of_ty ty) s
  | Pcast(_,e)     -> add_glob_expr s e
  | Pvar x         -> add_glob_var s x
  | Pget(x,e)      -> add_glob_expr (add_glob_var s x) e
  | Pload(_,x,e)   -> add_glob_expr (add_glob_var s x) e
  | Papp1(_, e)    -> add_glob_expr s e
  | Papp2(_,e1,e2) -> add_glob_expr (add_glob_expr s e1) e2
  | Pif(e,e1,e2)   -> add_glob_expr
                        (add_glob_expr
                           (add_glob_expr s e) e1) e2

let add_glob_exprs s es = List.fold_left add_glob_expr s es

let rec add_glob_lv s = function
  | Lnone _      -> s
  | Lvar x       -> add_glob_var s x
  | Lmem (_,x,e)
  | Laset (x,e)  -> add_glob_expr (add_glob_var s x) e

let add_glob_lvs s lvs = List.fold_left add_glob_lv s lvs

let rec add_glob_instr s i =
  match i.i_desc with
  | Cassgn(x, _, _, e) -> add_glob_expr (add_glob_lv s x) e
  | Copn(x,_,_,e) -> add_glob_exprs (add_glob_lvs s x) e
  | Cif(e,c1,c2) -> add_glob_body (add_glob_body (add_glob_expr s e) c1) c2
  | Cfor(x,(_,e1,e2), c) ->
    add_glob_body (add_glob_expr (add_glob_expr (add_glob_var s x) e1) e2) c
  | Cwhile(c,e,c')    -> add_glob_body (add_glob_expr (add_glob_body s c') e) c
  | Ccall(_,x,_,e) -> add_glob_exprs (add_glob_lvs s x) e

and add_glob_body s c =  List.fold_left add_glob_instr s c

let get_wsize = function
  | Type.Coq_sword sz -> sz
  | _ -> raise (Aint_error "Not a Coq_sword")

let swap_op2 op e1 e2 =
  match op with
  | E.Ogt   _ -> e2, e1
  | E.Oge   _ -> e2, e1
  | _         -> e1, e2


(*********************)
(* Safety conditions *)
(*********************)

(* TODO: some code from toEC.ml modified *)

type safe_cond =
  | Initv of var
  | Initai of var * expr
  | Inita of var * int
  | InBound of int * expr
  | Valid of wsize * ty gvar * expr
  | NotZero of wsize * expr

let add64 x e = Papp2 (E.Oadd ( E.Op_w Type.U64), Pvar x, e)

let in_bound x e =
  match (L.unloc x).v_ty with
  | Arr(_,n) -> InBound(n,e)
  | _ -> assert false

let safe_op2 e2 = function
  | E.Oand | E.Oor | E.Oadd _ | E.Omul _ | E.Osub _
  | E.Oland _ | E.Olor _ | E.Olxor _
  | E.Olsr _ | E.Olsl _ | E.Oasr _
  | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ -> []
  | E.Odiv E.Cmp_int -> []
  | E.Omod Cmp_int  -> []
  | E.Odiv (E.Cmp_w(_, s)) -> [NotZero (s, e2)]
  | E.Omod (E.Cmp_w(_, s)) -> [NotZero (s, e2)]

(* let well_shaped = function
 *   | *)

let safe_var x = match (L.unloc x).v_ty with
  | Arr(_,n) -> Inita (L.unloc x, n)
  | _ -> Initv(L.unloc x)

let rec safe_e_rec safe = function
  | Pconst _ | Pbool _ | Parr_init _ | Pglobal _ -> safe
  | Pvar x -> safe_var x :: safe

  | Pload (ws,x,e) -> Valid (ws, L.unloc x, e) :: safe_e_rec safe e
  | Pcast (_, e) | Papp1 (_, e) -> safe_e_rec safe e
  | Pget (x, e) -> in_bound x e :: Initai(L.unloc x, e) :: safe
  | Papp2 (op, e1, e2) -> safe_op2 e2 op @ safe_e_rec (safe_e_rec safe e1) e2
  | Pif  (e1, e2, e3) ->
    (* We do not check "is_defined e1 && is_defined e2" since
        (safe_e_rec (safe_e_rec safe e1) e2) implies it *)
    safe_e_rec (safe_e_rec (safe_e_rec safe e1) e2) e3

let safe_e = safe_e_rec []

let safe_es = List.fold_left safe_e_rec []

let safe_lval = function
  | Lnone _ | Lvar _ -> []
  | Lmem(ws, x, e) -> Valid (ws, L.unloc x, e) :: safe_e_rec [] e
  | Laset(x,e) -> in_bound x e :: safe_e_rec [] e

let safe_lvals = List.fold_left (fun safe x -> safe_lval x @ safe) []

let safe_opn safe opn es = match opn with
  | E.Omulu _ | E.Oaddcarry _ | E.Osubcarry _ | E.Oset0 _
  | E.Ox86_MOV _ | E.Ox86_MOVSX _ | E.Ox86_MOVZX _ | E.Ox86_MOVZX32
  | E.Ox86_CMOVcc _ | E.Ox86_ADD _ | E.Ox86_SUB _ | E.Ox86_MUL _ | E.Ox86_IMUL _
  | E.Ox86_IMULt _ | E.Ox86_IMULtimm _ -> safe

  | E.Ox86_DIV sz | E.Ox86_IDIV sz ->  NotZero (sz, List.nth es 2) :: safe

  | E.Ox86_CQO _ | E.Ox86_ADC _ | E.Ox86_SBB _ | E.Ox86_NEG _
  | E.Ox86_INC _ | E.Ox86_DEC _ | E.Ox86_SETcc | E.Ox86_BT _
  | E.Ox86_LEA _ | E.Ox86_TEST _ | E.Ox86_CMP _
  | E.Ox86_AND _ | E.Ox86_OR _ | E.Ox86_XOR _ | E.Ox86_NOT _
  | E.Ox86_ROL _ | E.Ox86_ROR _ | E.Ox86_SHL _ | E.Ox86_SHR _ | E.Ox86_SAR _
  | E.Ox86_SHLD _ | E.Ox86_SHRD _ | E.Ox86_BSWAP _ | E.Ox86_MOVD _
  | E.Ox86_VMOVDQU _ | E.Ox86_VPAND _ | E.Ox86_VPANDN _
  | E.Ox86_VPOR _ | E.Ox86_VPXOR _ | E.Ox86_VPADD _
  | E.Ox86_VPMULU _ | E.Ox86_VPEXTR _ | E.Ox86_VPINSR _
  | E.Ox86_VPSLL _ | E.Ox86_VPSRL _ | E.Ox86_VPSLLV _ | E.Ox86_VPSRLV _
  | E.Ox86_VPSLLDQ _ | E.Ox86_VPSRLDQ _
  | E.Ox86_VPSHUFB _ | E.Ox86_VPSHUFHW _
  | E.Ox86_VPSHUFLW _ | E.Ox86_VPSHUFD _ | E.Ox86_VPUNPCKH _ | E.Ox86_VPUNPCKL _
  | E.Ox86_VPBLENDD _ | E.Ox86_VPBROADCAST _
  | E.Ox86_VBROADCASTI128 | E.Ox86_VEXTRACTI128 | E.Ox86_VINSERTI128
  | E.Ox86_VPERM2I128 | E.Ox86_VPERMQ -> safe

let safe_instr ginstr = match ginstr.i_desc with
  | Cassgn (lv, _, _, e) -> safe_e_rec (safe_lval lv) e
  | Copn (lvs,_,opn,es) -> safe_opn (safe_lvals lvs @ safe_es es) opn es
  | Cif(e, _, _) -> safe_e e
  | Cwhile(_, _, _) -> []       (* We check the while condition later. *)
  | Ccall(_, lvs, _, es) -> safe_lvals lvs @ safe_es es
  | Cfor (_, (_, e1, e2), _) -> safe_es [e1;e2]

let safe_return main_decl =
  List.fold_left (fun acc v -> safe_var v :: acc) [] main_decl.f_ret


(*********)
(* Utils *)
(*********)

let obind2 f x y = match x, y with
  | Some u, Some v -> f u v
  | _ -> None

let oget = function
  | Some x -> x
  | None -> raise (Failure "Oget")

let mvar_of_var v = match v.v_ty with
  | Bty _ -> Mvalue (Avar v)
  | Arr _ -> Mvalue (Aarray v)

let wsize_of_ty ty = match ty with
  | Bty Bool -> assert false
  | Bty Int -> -1
  | Bty (U sz) -> int_of_ws sz
  | Arr (sz, _) -> int_of_ws sz

let rec combine3 l1 l2 l3 = match l1,l2,l3 with
  | h1 :: t1, h2 :: t2, h3 :: t3 -> (h1,h2,h3) :: combine3 t1 t2 t3
  | [], [], [] -> []
  | _ -> raise (Invalid_argument "combine3")

let rec add_offsets assigns = match assigns with
  | [] -> []
  | (Mvalue (Avar v)) :: tail ->
    (Mvalue (Avar v)) :: (MvarOffset v) :: add_offsets tail
  | u :: tail -> u :: add_offsets tail

let rec add_offsets3 assigns = match assigns with
  | [] -> []
  | (ty, Mvalue (Avar v),es) :: tail ->
    (ty, Mvalue (Avar v),es)
    :: (ty, MvarOffset v,es)
    :: add_offsets3 tail
  | u :: tail -> u :: add_offsets3 tail

let get_fun_def prog f = List.find_opt (fun x -> x.f_name = f) (snd prog)

let fun_locals f_decl =
  let locals = Sv.elements (locals f_decl) in
  List.map mvar_of_var locals
  |> expand_arr_vars
  |> add_offsets

let fun_args_no_offset f_decl = List.map mvar_of_var f_decl.f_args
                      |> expand_arr_vars

let fun_args f_decl = fun_args_no_offset f_decl |> add_offsets

let in_cp_var v = match v with
  | Mvalue (Avar v) -> Some (MinValue v)
  | _ -> None

let fun_in_args_no_offset f_decl =
  fun_args_no_offset f_decl |> List.map in_cp_var

let fun_in_args f_decl = fun_args f_decl |> List.map in_cp_var

let fun_rets_no_offsets f_decl =
  List.map (fun x -> L.unloc x |> mvar_of_var) f_decl.f_ret
  |> expand_arr_vars

let get_mem_range env = List.map (fun x -> MmemRange x) env.m_locs

let prog_globals env =
  List.map (fun (_,(s,ty)) -> Mglobal (s, Conv.ty_of_cty ty))
    (Ms.bindings env.s_glob)
  @ get_mem_range env
  |> expand_arr_vars
  |> add_offsets

let fun_vars f_decl env =
  fun_args f_decl
  @ prog_globals env
  @ fun_locals f_decl


(****************************)
(* Expression Linearization *)
(****************************)

(* TODO: careful with signed words. Look at jasmin_word.ec *)
let op1_to_abs_unop op1 = match op1 with
  | E.Oneg _   -> Some Texpr1.Neg
  | _ -> None


let op2_to_abs_binop op2 = match op2 with
  | E.Oadd _ -> Some Texpr1.Add
  | E.Omul _ -> Some Texpr1.Mul
  | E.Osub _ -> Some Texpr1.Sub
  | E.Omod _ -> Some Texpr1.Mod

  | E.Odiv _ -> None
  | E.Oand | E.Oor
  | E.Oland _ | E.Olor _ | E.Olxor _ (* bit-wise boolean connectives *)
  | E.Olsr _ | E.Olsl _ | E.Oasr _
  | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ -> None


(* Return lin_expr mod 2^n *)
let expr_pow_mod apr_env n lin_expr =
  let mod_expr = cst_pow_minus apr_env n 0 in
  Mtexpr.binop Texpr1.Mod lin_expr mod_expr

let word_interval signed ws =
  if signed then
    (* TODO: add signed words *)
    assert false
  else
    let up_mpq = mpq_pow_minus ws 1 in
    Interval.of_mpqf (Mpqf.of_int 0) up_mpq

(* We wrap lin_expr as an out_i word.
   On unsigned word, we do:
   ((lin_expr % 2^n) + 2^n) % 2^n) *)
(* TODO: this is correct only on unsigned words *)
let wrap_lin_expr apr_env n lin_expr =
  let expr = expr_pow_mod apr_env n lin_expr in

  let pow_expr = cst_pow_minus apr_env n 0 in
  let expr' = Mtexpr.binop Texpr1.Add expr pow_expr in

  expr_pow_mod apr_env n expr'



let print_not_word_expr e =
  Format.eprintf "@[<v>Should be a word expression:@;\
                  @[%a@]@;Type:@;@[%a@]@]@."
    (Printer.pp_expr ~debug:(!Glob_options.debug)) e
    (Printer.pp_ty) (Conv.ty_of_cty (ty_expr e))

let check_is_int v = match v.v_ty with
  | Bty Int -> ()
  | _ ->
    Format.eprintf "%s should be an int but is a %a"
      v.v_name Printer.pp_ty v.v_ty;
    raise (Aint_error "Bad type")

let check_is_word v = match v.v_ty with
  | Bty (U _) -> ()
  | _ ->
    Format.eprintf "%s should be a word but is a %a"
      v.v_name Printer.pp_ty v.v_ty;
    raise (Aint_error "Bad type")

let map_f f e_opt = match e_opt with
  | None -> None
  | Some (b,el,er) -> Some (b, f el, f er)


(*********************)
(* Abstract Iterator *)
(*********************)

(* Locations of the abstract iterator *)
type it_loc =
  | ItFunIn of funname * L.t   (* call-site sensitive function call *)

module ItKey = struct
  type t = it_loc

  let compare = Pervasives.compare
end

module ItMap = Map.Make(ItKey)


(************************)
(* Abstract Interpreter *)
(************************)

module AbsInterpreter (AbsDom : AbsNumBoolType) : sig
  val analyze : unit func -> unit prog -> bool
end = struct
  type astate = { it : (AbsDom.t * AbsDom.t) ItMap.t;
                  abs : AbsDom.t;
                  env : s_env;
                  prog : unit prog;
                  violation : bool }


  let app_abs f state = { state with abs = f state.abs }
  (* Try to evaluate e to a constant expression in abs *)
  let rec aeval_cst_int abs e = match e with
    | Pvar x ->
      check_is_int (L.unloc x);
      let int = AbsDom.bound_variable abs (mvar_of_var (L.unloc x)) in
      if Scalar.equal int.inf int.sup then
        let tent_i = match int.inf with
          | Scalar.Float f -> int_of_float f
          | Scalar.Mpqf q -> Mpqf.to_float q |> int_of_float
          | Scalar.Mpfrf f -> Mpfrf.to_float f |> int_of_float in
        if Scalar.cmp_int int.inf tent_i = 0 then Some tent_i
        else begin Format.eprintf "%a@." Interval.print int; None end
      else begin Format.eprintf "%a@." Interval.print int; None end

    | Pconst c -> Some (B.to_int c)

    | Papp1 (E.Oneg Op_int, e) ->
      obind (fun x -> Some (- x)) (aeval_cst_int abs e)

    | Papp2 (Oadd Op_int, e1, e2) ->
      obind2 (fun x y -> Some (x + y))
        (aeval_cst_int abs e1) (aeval_cst_int abs e2)

    | Papp2 (Osub Op_int, e1, e2) ->
      obind2 (fun x y -> Some (x - y))
        (aeval_cst_int abs e1) (aeval_cst_int abs e2)

    | Papp2 (Omul Op_int, e1, e2) ->
      obind2 (fun x y -> Some (x * y))
        (aeval_cst_int abs e1) (aeval_cst_int abs e2)

    | _ -> None

    (* We could do better here, with major changes to the analysis:
     - return an Intervar.t instead of an int.
     - extend Mtexpr.to_aexpr to return a Texpr1.t and a list of
     non-deterministic assignments *)
  let rec array_range abs ei = match aeval_cst_int abs ei with
    | Some i -> i
    | None -> raise (Aint_error "Array access offset could not be \
                                   determined statically")

  (* Collect all variables appearing in e. *)
  let pt_expr_of_expr abs e =
    let exception Expr_contain_load in
    let rec aux acc e = match e with
      | Pbool _ | Parr_init _ | Pconst _ -> acc

      | Pvar x -> mvar_of_var (L.unloc x) :: acc
      | Pglobal (ws,x) -> Mglobal (x,Bty (U ws)) :: acc
      | Pget(x,ei) ->
        let int = array_range abs ei in
        Mvalue (AarrayEl (L.unloc x, int )) :: acc

      | Pcast (_,e1) | Papp1 (_, e1) -> aux acc e1

      | Pload _ -> raise Expr_contain_load

      | Pif (_,e1,e2) | Papp2 (_, e1, e2) -> aux (aux acc e1) e2 in

    try PtVars (aux [] e) with Expr_contain_load -> PtTop


  (* Return true iff the linear expression overflows *)
  let linexpr_overflow abs lin_expr signed ws =
    let int = AbsDom.bound_texpr abs lin_expr in
    let ws_int = word_interval signed ws in

    not (Interval.is_leq int ws_int)

  (* TODO: signed words *)
  let wrap_if_overflow abs e _ ws =
    if linexpr_overflow abs e false ws then
      wrap_lin_expr (AbsDom.get_env abs) ws e
    else e

  (* Casting: lin_expr is a in_i word, and we cast it as an out_i word. *)
  (* TODO: signed words *)
  let cast_if_overflows abs out_i in_i lin_expr =
    assert ((out_i <> -1)  && (in_i <> -1));
    if out_i <= in_i then
      wrap_if_overflow abs lin_expr false out_i
    else
      wrap_if_overflow abs lin_expr false in_i


  exception Unop_not_supported of E.sop1

  exception Binop_not_supported of E.sop2

  exception If_not_supported

  let rec linearize_iexpr abs (e : expr) =
    let apr_env = AbsDom.get_env abs in
    match e with
    | Pconst z ->
      let mpq_z = Mpq.init_set_str (B.to_string z) ~base:10 in
      Mtexpr.cst apr_env (Coeff.s_of_mpq mpq_z)

    | Pvar x ->
      check_is_int (L.unloc x);
      Mtexpr.var apr_env (Mvalue (Avar (L.unloc x)))

    | Papp1 (op1, e1) ->
      begin match op1_to_abs_unop op1 with
        | Some absop ->
          Mtexpr.unop absop (linearize_iexpr abs e1)

        | None -> raise (Unop_not_supported op1) end

    | Papp2 (op2, e1, e2) ->
      begin match op2_to_abs_binop op2 with
        | Some absop ->
          Mtexpr.(binop absop
                    (linearize_iexpr abs e1)
                    (linearize_iexpr abs e2))

        | None -> raise (Binop_not_supported op2) end

    | Pif _ -> raise If_not_supported

    | _ -> assert false


  and linearize_wexpr abs (e : ty gexpr) =
    let apr_env = AbsDom.get_env abs in
    match e with
    | Pvar x ->
      check_is_word (L.unloc x);
      Mtexpr.var apr_env (Mvalue (Avar (L.unloc x)))

    | Pglobal(ws, x) ->
      let abs_expr1 = Mtexpr.var apr_env (Mglobal (x,Bty (U ws))) in
      abs_expr1

    | Papp1 (op1, e1) ->
      begin match op1_to_abs_unop op1 with
        | Some absop ->
          Mtexpr.unop absop (linearize_wexpr abs e1)

        | None -> raise (Unop_not_supported op1) end

    | Papp2 (op2, e1, e2) ->
      begin match op2_to_abs_binop op2 with
        | Some Texpr1.Mod -> begin match op2 with
            | E.Omod (Cmp_w (_,ws))  ->
              let l_e1 = linearize_wexpr abs e1 in
              (* TODO: signed words *)
              let w_e1 = wrap_if_overflow abs l_e1 false (int_of_ws ws) in

              let l_e2 = linearize_wexpr abs e2 in
              let w_e2 = wrap_if_overflow abs l_e2 false (int_of_ws ws) in

              Mtexpr.(binop Texpr1.Mod w_e1 w_e2)

            | _ ->
              raise (Aint_error "linearize_wexpr : Papp2 : bad type") end

        | Some Texpr1.Add | Some Texpr1.Mul | Some Texpr1.Sub as absop->
          Mtexpr.(binop (oget absop)
                    (linearize_wexpr abs e1)
                    (linearize_wexpr abs e2))

        | Some Texpr1.Div | Some Texpr1.Pow | None ->
          raise (Binop_not_supported op2) end

    | Pcast(sz,e1) -> begin match ty_expr e1 with
        | Type.Coq_sint ->
          let abs_expr1 = linearize_iexpr abs e1 in
          wrap_if_overflow abs abs_expr1 false (int_of_ws sz)

        | Type.Coq_sword _ ->
          let in_size = get_wsize (ty_expr e1) in
          let abs_expr1 = linearize_wexpr abs e1 in
          cast_if_overflows abs (int_of_ws sz) (int_of_ws in_size) abs_expr1

        | _ ->  print_not_word_expr e1;
          raise (Aint_error "linearize_wexpr : cast : bad type") end

    | Pget(x,ei) ->
      let int = array_range abs ei in
      Mtexpr.var apr_env (Mvalue (AarrayEl (L.unloc x, int )))

    | Pload _ ->
      (* We return top on loads *)
      let apr_env = AbsDom.get_env abs in
      Mtexpr.cst apr_env (Coeff.Interval Interval.top)

    | _ -> print_not_word_expr e;
      assert false

  let rec remove_if_expr_aux : 'a Prog.gexpr ->
    ('a Prog.gexpr * 'a Prog.gexpr * 'a Prog.gexpr) option = function
    | Pif(e1,et,ef) -> Some (e1,et,ef)

    | Pconst _  | Pbool _ | Parr_init _ | Pvar _ | Pglobal _ -> None

    | Pcast(sz,e1) ->
      remove_if_expr_aux e1
      |> map_f (fun ex -> Pcast(sz,ex))

    | Pget(x,e1) ->
      remove_if_expr_aux e1
      |> map_f (fun ex -> Pget(x,ex))

    | Pload (sz, x, e1) ->
      remove_if_expr_aux e1
      |> map_f (fun ex -> Pload (sz,x,ex))

    | Papp1 (op1, e1) ->
      remove_if_expr_aux e1
      |> map_f (fun ex -> Papp1 (op1,ex))

    | Papp2 (op2, e1, e2) ->
      match remove_if_expr_aux e1 with
      | Some _ as e_opt -> map_f (fun ex -> Papp2 (op2, ex, e2)) e_opt
      | None -> remove_if_expr_aux e2
                |> map_f (fun ex -> Papp2 (op2, e1, ex))


  let rec remove_if_expr (e : 'a Prog.gexpr) = match remove_if_expr_aux e with
    | Some (b,el,er) ->
      List.map (fun (l_bool,expr) ->
          (b :: l_bool,expr))
        (remove_if_expr el)
      @ (List.map (fun (l_bool,expr) ->
          ((Papp1 (E.Onot,b)) :: l_bool,expr))
          (remove_if_expr er))
    | None -> [([],e)]

  let opk_of_cmpk = function
    | E.Cmp_int -> E.Op_int
    | E.Cmp_w (_,ws) -> E.Op_w ws

  (* TODO: unsound on signed operations *)
  let op2_to_typ op2 = match op2 with
    | E.Oand | E.Oor | E.Oadd _ | E.Omul _ | E.Osub _
    | E.Odiv _ | E.Omod _ | E.Oland _ | E.Olor _
    | E.Olxor _ | E.Olsr _ | E.Olsl _ | E.Oasr _ -> assert false

    | E.Oeq k -> (Tcons1.EQ, k)
    | E.Oneq k -> (Tcons1.DISEQ, k)
    | E.Olt k -> (Tcons1.SUP, opk_of_cmpk k)
    | E.Ole k -> (Tcons1.SUPEQ, opk_of_cmpk k)
    | E.Ogt k -> (Tcons1.SUP, opk_of_cmpk k)
    | E.Oge k -> (Tcons1.SUPEQ, opk_of_cmpk k)

  let rec bexpr_to_btcons_aux : AbsDom.t -> 'a Prog.gexpr -> btcons =
    fun abs e ->
      let aux = bexpr_to_btcons_aux abs in
      match e with
        | Pbool b ->
          let cons =
            if b then true_tcons1 (AbsDom.get_env abs)
            else false_tcons1 (AbsDom.get_env abs) in
          BLeaf cons

        | Pvar x -> BVar (string_of_mvar (Mvalue (Avar (L.unloc x))), true)

        | Pglobal _ -> assert false (* Global variables are of type word *)

        | Pif(e1,et,ef) ->
          let bet, bef, be1 = aux et, aux ef, aux e1 in
          let be1_f = match flip_btcons be1 with
            | Some c -> c
            | None -> raise Bop_not_supported in

          BOr ( BAnd(be1,bet), BAnd(be1_f,bef) )

        | Papp1 (op1, e1) -> begin match op1 with
            | E.Onot ->
              let be1 = aux e1 in
              begin match flip_btcons be1 with
                | Some c -> c
                | None -> raise Bop_not_supported end
            | _ -> assert false end

        | Papp2 (op2, e1, e2) -> begin match op2 with
            | E.Oadd _ | E.Omul _ | E.Osub _
            | E.Odiv _ | E.Omod _ | E.Oland _ | E.Olor _
            | E.Olxor _ | E.Olsr _ | E.Olsl _ | E.Oasr _ -> assert false

            | E.Oand -> BAnd ( aux e1, aux e2 )

            | E.Oor -> BOr ( aux e1, aux e2 )

            (* TODO: this is unsound on signed words *)
            | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ ->
              match remove_if_expr_aux e with
              | Some (eb,el,er)  -> aux (Pif (eb,el,er))
              | None -> flat_bexpr_to_btcons abs op2 e1 e2 end

        | _ -> assert false

  and flat_bexpr_to_btcons abs op2 e1 e2 =
    let e1',e2' = swap_op2 op2 e1 e2 in
    let lincons, kind = op2_to_typ op2 in

    try let expr = match kind with
        | E.Op_int ->
          let lin1 = linearize_iexpr abs e1'
          and lin2 = linearize_iexpr abs e2' in

          Mtexpr.(binop Sub lin2 lin1)

        | E.Op_w ws ->
          let lin1 = match ty_expr e1' with
            | Coq_sint -> linearize_iexpr abs e1'
            | Coq_sword _ -> linearize_wexpr abs e1'
            | _ -> assert false
          and lin2 = match ty_expr e2' with
            | Coq_sint -> linearize_iexpr abs e2'
            | Coq_sword _ -> linearize_wexpr abs e2'
            | _ -> assert false in

          (* TODO: signed words *)
          let lin1 = wrap_if_overflow abs lin1 false (int_of_ws ws)
          and lin2 = wrap_if_overflow abs lin2 false (int_of_ws ws) in

          Mtexpr.(binop Sub lin2 lin1) in

      BLeaf (Mtcons.make expr lincons)
    with Unop_not_supported _ | Binop_not_supported _ ->
      raise Bop_not_supported


  let bexpr_to_btcons : 'a Prog.gexpr -> AbsDom.t -> btcons option =
    fun e abs -> try Some (bexpr_to_btcons_aux abs e) with
        Bop_not_supported -> None


  let linearize_if_iexpr : 'a Prog.gexpr -> AbsDom.t -> s_expr =
    fun e abs ->
      List.map (fun (bexpr_list, expr) ->
          let f x = bexpr_to_btcons x abs in
          let b_list = List.map f bexpr_list in

          let b_list =
            if List.exists (fun x -> x = None) b_list then []
            else List.map oget b_list in

          let lin_expr = try Some (linearize_iexpr abs expr) with
            | Unop_not_supported _ | Binop_not_supported _ -> None in

          (b_list, lin_expr))
        (remove_if_expr e)

  let linearize_if_wexpr : int -> ty gexpr -> AbsDom.t -> s_expr =
    fun out_sw e abs ->
      List.map (fun (bexpr_list, expr) ->
          let f x = bexpr_to_btcons x abs in
          let b_list = List.map f bexpr_list in

          let b_list =
            if List.exists (fun x -> x = None) b_list then []
            else List.map oget b_list in

          let in_sw = get_wsize (ty_expr e) in

          let lin_expr =
            try linearize_wexpr abs expr
                |> cast_if_overflows abs out_sw (int_of_ws in_sw)
                |> some
            with | Unop_not_supported _ | Binop_not_supported _ -> None in

          (b_list, lin_expr))
        (remove_if_expr e)

  let rec linearize_if_expr : int -> 'a Prog.gexpr -> AbsDom.t -> s_expr =
    fun out_ws e abs ->
    match ty_expr e with
    | Coq_sint ->
      assert (out_ws = -1);
      linearize_if_iexpr e abs

    | Coq_sword _ -> linearize_if_wexpr out_ws e abs

    | Coq_sbool -> assert false
    | Coq_sarr _ -> assert false


  let init_env : 'info prog -> mem_loc list -> s_env =
    fun (glob_decls, fun_decls) mem_locs ->
    let env = { s_glob = Ms.empty; m_locs = mem_locs } in
    let env =
      List.fold_left (fun env (ws, x, _) -> add_glob env x ws)
        env glob_decls in

    List.fold_left (fun env f_decl ->
        { env with s_glob = List.fold_left (fun s_glob ginstr ->
              add_glob_instr s_glob ginstr)
              env.s_glob f_decl.f_body })
      env fun_decls

  let init_args f_args state =
    List.fold_left (fun state v -> match v with
        | Mvalue at -> { state with abs = AbsDom.is_init state.abs at }
        | _ -> state )
      state f_args

  let set_zeros f_args abs =
    List.fold_left (fun abs v -> match v with
        | MvarOffset _ | MmemRange _ ->
          let env = AbsDom.get_env abs in
          let z_expr = Mtexpr.cst env (Coeff.s_of_int 0) in
          let z_sexpr = sexpr_from_simple_expr z_expr in
          AbsDom.assign_sexpr ~force:true abs v z_sexpr
        | _ -> abs)
      abs f_args


  let set_bounds f_args abs =
    List.fold_left (fun abs v ->
        let ws = match v with
          | Mvalue (AarrayEl (t,_)) -> Some (arr_size t)
          | Mvalue (Avar gv) -> begin match gv.v_ty with
              | Bty (U ws) -> Some ws
              | _ -> None end
          | _ -> None in

        (* TODO: for signed words, set the correct bounds here *)
        if ws <> None then
          let int = word_interval false (oget ws |> int_of_ws)
          and env = AbsDom.get_env abs in
          let z_expr = Mtexpr.cst env (Coeff.Interval int) in
          let z_sexpr = sexpr_from_simple_expr z_expr in

          AbsDom.assign_sexpr abs v z_sexpr
        else abs)
      abs f_args

  let init_state : unit func -> unit prog -> astate =
    fun main_decl (glob_decls, fun_decls) ->
      let mem_locs = List.map (fun x -> MemLoc x) main_decl.f_args in
      let env = init_env (glob_decls, fun_decls) mem_locs in
      let it = ItMap.empty in

      (* We add the initial variables *)
      let f_args = fun_args main_decl
      and f_in_args = fun_in_args main_decl
      and m_locs = List.map (fun mloc -> MmemRange mloc ) env.m_locs in

      (* We set the offsets and ranges to zero, and bound the variables using
         their types. E.g. register of type U 64 is in [0;2^64]. *)
      let abs = AbsDom.make (f_args @ m_locs) mem_locs
                |> set_zeros (f_args @ m_locs)
                |> set_bounds f_args
      in

      (* We extend the environment to its local variables *)
      let f_vars = (List.map otolist f_in_args |> List.flatten)
                   @ fun_vars main_decl env in
      let abs = AbsDom.change_environment abs f_vars in

      (* We keep track of the initial values. *)
      let abs = List.fold_left2 (fun abs x oy -> match oy with
          | None -> abs
          | Some y ->
            let sexpr = Mtexpr.var (AbsDom.get_env abs) x
                        |> sexpr_from_simple_expr in
            AbsDom.assign_sexpr abs y sexpr)
          abs f_args f_in_args in

      { it = it; abs = abs; env = env;
        prog = (glob_decls, fun_decls);
        violation = false }
      |> init_args (fun_args main_decl)

  (* Checks that all safety conditions hold, except for valid memory access. *)
  let rec is_safe state = function
    | Initv v -> begin match mvar_of_var v with
        | Mvalue at -> AbsDom.check_init state.abs at
        | _ -> assert false end

    | Inita (v,i) -> begin match mvar_of_var v with
        | Mvalue (Aarray v) ->
          let vels = List.init i (fun n -> AarrayEl (v,n)) in
          List.for_all (AbsDom.check_init state.abs) vels
        | _ -> assert false end

    | Initai (v,e) -> begin match mvar_of_var v with
        | Mvalue (Aarray v) ->
          let i = array_range state.abs e in
          AbsDom.check_init state.abs (AarrayEl (v,i))
        | _ -> assert false end

    | InBound (i,e) ->
      (* We check that e is no larger than i *)
      let be = Papp2 (E.Oge E.Cmp_int, e, Pconst (B.of_int i)) in
      begin match bexpr_to_btcons be state.abs with
        | None -> false
        | Some c -> AbsDom.is_bottom (AbsDom.meet_btcons state.abs c) end

    | NotZero (ws,e) ->
      (* We check that e is never 0 *)
      let be = Papp2 (E.Oeq (E.Op_w ws), e, Pcast (ws,Pconst (B.of_int 0))) in
      begin match bexpr_to_btcons be state.abs with
        | None -> false
        | Some c -> AbsDom.is_bottom (AbsDom.meet_btcons state.abs c) end

    | Valid _ -> true

  (* Update abs with the abstract memory range for memory accesses. *)
  let rec mem_safety_apply abs = function
    | Valid (ws,x,e) ->
      let pts = AbsDom.var_points_to abs (mvar_of_var x) in
      if List.length pts = 1 then
        let pt = List.hd pts in
        let x_o = Mtexpr.var (AbsDom.get_env abs) (MvarOffset x) in
        let lin_e = linearize_wexpr abs e in
        let c_ws =
          ((int_of_ws ws) / 8)
          |> Coeff.s_of_int
          |> Mtexpr.cst (AbsDom.get_env abs) in
        let ws_plus_e = Mtexpr.binop Texpr1.Add c_ws lin_e in
        let sexpr = Mtexpr.binop Texpr1.Add x_o ws_plus_e
                    |> sexpr_from_simple_expr in

        AbsDom.assign_sexpr abs (MmemRange pt) sexpr
      else assert false         (* TEMP abs *)
    | _ -> abs

  let rec check_safety_rec state unsafe = function
    | [] -> unsafe
    | c :: t ->
      if is_safe state c then check_safety_rec state unsafe t
      else check_safety_rec state (c :: unsafe) t

  let rec mem_safety_rec abs = function
    | [] -> abs
    | c :: t -> mem_safety_rec (mem_safety_apply abs c) t

  let pp_var = Printer.pp_var ~debug:false
  let pp_expr = Printer.pp_expr ~debug:false
  let pp_ws fmt ws = Format.fprintf fmt "%i" (int_of_ws ws)

  let pp_safety_cond fmt = function
    | Initv x -> Format.fprintf fmt "is_init %a" pp_var x
    | Initai(x,e) -> Format.fprintf fmt "is_init %a.[%a]" pp_var x pp_expr e
    | Inita(x,n) -> Format.fprintf fmt "is_init[%i] %a" n pp_var x
    | NotZero(sz,e) -> Format.fprintf fmt "%a <>%a zero" pp_expr e pp_ws sz
    | InBound(n,e)  -> Format.fprintf fmt "in_bound %a %i" pp_expr e n
    | Valid (sz, x, e) ->
      Format.fprintf fmt "is_valid %s + %a W%a" x.v_name pp_expr e pp_ws sz

  let rec check_safety state conds =
    let unsafe = check_safety_rec state [] conds in
    let state =
      if unsafe <> [] then begin
        Format.eprintf "@[<v>Safety Violation(s):@;@[<v>%a@]@;@]@."
          (pp_list pp_safety_cond) unsafe;
        { state with violation = true } end
      else state in

    let abs = mem_safety_rec state.abs conds in
    { state with abs = abs }

  (* Return te mvar where the abstract assignment takes place. For now, no
     abstraction of the memory. *)
  let mvar_of_lvar abs lv = match lv with
    | Lnone _ -> None
    | Lmem _ -> None
    | Lvar x  ->
      let ux = L.unloc x in
      begin match ux.v_kind, ux.v_ty with
        | Global,_ -> Mglobal (ux.v_name,ux.v_ty) |> some
        | _, Bty _ -> Mvalue (Avar ux) |> some
        | _, Arr _ -> Mvalue (Aarray ux) |> some end

    | Laset (x,ei) ->
      let int = array_range abs ei in
      Mvalue (AarrayEl (L.unloc x, int)) |> some

  let ty_gvar_of_mvar = function
    | Mvalue (Avar v) -> Some v
    | _ -> None

  let apply_offset_expr abs outmv inv offset_expr =
    match ty_gvar_of_mvar outmv with
    | None -> abs
    | Some outv ->
      let env = AbsDom.get_env abs in
      let inv_os = Mtexpr.var env (MvarOffset inv) in

      let off_e = linearize_wexpr abs offset_expr
      and e_ws = get_wsize (ty_expr offset_expr) in
      let wrap_off_e = wrap_if_overflow abs off_e false (int_of_ws e_ws) in

      let sexpr =
        Mtexpr.binop Texpr1.Add inv_os wrap_off_e
        |> sexpr_from_simple_expr in
      AbsDom.assign_sexpr abs (MvarOffset outv) sexpr

  let aeval_top_offset abs outmv = match ty_gvar_of_mvar outmv with
    | Some outv -> AbsDom.forget_list abs [MvarOffset outv]
    | None -> abs

  let valid_offset_var abs ws_o y =
    if ws_o = Bty (U (U64)) then
      let my = mvar_of_var (L.unloc y) in
      let y_pts = AbsDom.var_points_to abs my in
      List.length y_pts = 1
    else false

  (* Evaluate the offset abstraction *)
  let aeval_offset abs ws_o outmv e = match e with
    | Pvar y ->
      if valid_offset_var abs ws_o y then
        apply_offset_expr abs outmv (L.unloc y) (Pcast(U64,Pconst(B.of_int 0)))
      else aeval_top_offset abs outmv

    | Papp2 (op2,el,er) -> begin match op2,el with
        | E.Oadd ( E.Op_w Type.U64), Pvar y ->
          if valid_offset_var abs ws_o y then
            apply_offset_expr abs outmv (L.unloc y) er
          else aeval_top_offset abs outmv

        | _ -> aeval_top_offset abs outmv end

    | _ -> aeval_top_offset abs outmv

  (* Array assignment. Does the numerical and points-to assignments. *)
  let assign_arr_expr a v e = match v with
    | Mvalue (Aarray gv) -> begin match Mtexpr.(e.mexpr) with
        | Mtexpr.Mvar (Mvalue (Aarray ge)) ->
          let n = arr_range gv in
          assert (n = arr_range ge);
          assert (arr_size gv = arr_size ge);
          List.fold_left (fun a i ->
              let vi = Mvalue (AarrayEl (gv,i))  in
              let eiv = Mvalue (AarrayEl (ge,i)) in
              let ei = Mtexpr.var (AbsDom.get_env a) eiv
                       |> sexpr_from_simple_expr in

              (* Numerical abstraction *)
              let a = AbsDom.assign_sexpr a vi ei in
              (* Points-to abstraction *)
              AbsDom.assign_pt_expr a vi (PtVars [eiv]))
            a (List.init n (fun i -> i))

        | _ -> assert false end
    | _ -> assert false


  (* Abstract evaluation of an assignment *)
  let abs_assign : astate -> 'a gty -> mvar option -> ty gexpr -> astate =
    fun state out_ty out_mvar e -> match ty_expr e, out_mvar with
      | _, None -> state

      | Coq_sint, Some mvar | Coq_sword _, Some mvar ->
        (* Numerical abstraction *)
        let lv_s = wsize_of_ty out_ty in
        let s_expr = linearize_if_expr lv_s e state.abs in
        let abs = AbsDom.assign_sexpr state.abs mvar s_expr in

        (* Points-to abstraction *)
        let pt_expr = pt_expr_of_expr state.abs e in
        let abs = AbsDom.assign_pt_expr abs mvar pt_expr in

        (* Offset abstraction *)
        let abs = aeval_offset abs out_ty mvar e in

        { state with abs = abs }

      | Coq_sbool, Some mvar ->
        begin let svar = string_of_mvar mvar in
          match bexpr_to_btcons e state.abs with
          | None -> { state with abs = AbsDom.forget_bvar state.abs svar }
          | Some btcons ->
            let abs' = AbsDom.assign_bexpr state.abs svar btcons in
            { state with abs = abs' } end

      | Coq_sarr _, Some mvar ->
        match e with
        | Pvar x ->
          let apr_env = AbsDom.get_env state.abs in
          let se = Mtexpr.var apr_env (Mvalue (Aarray (L.unloc x))) in
          begin match mvar with
            | Mvalue (Aarray _) | Temp _ ->
              { state with abs = assign_arr_expr state.abs mvar se }
            | _ -> assert false end

        | Parr_init _ -> state
        | _ ->
          Format.eprintf "@[%a@]@." (Printer.pp_expr ~debug:true) e;
          assert false

  let init_lv lv state = match mvar_of_lvar state.abs lv with
    | Some (Mvalue at) -> { state with abs = AbsDom.is_init state.abs at }
    | _ -> state

  let init_lvs lvs s = List.fold_left (fun s lv -> init_lv lv s) s lvs

  let offsets_of_mvars l = List.map ty_gvar_of_mvar l
                           |> List.filter (fun x -> x <> None)
                           |> List.map (fun x -> MvarOffset (oget x))

  (* Prepare the caller for a function call. Returns the state with the
     arguments es evaluated in f input variables. *)
  let aeval_f_args state f es =
    let f_decl = get_fun_def state.prog f |> oget in

    let f_args = fun_args_no_offset f_decl
    and exp_es = expand_arr_exprs es
    and exp_in_tys = f_decl.f_tyin |> expand_arr_tys in

    let assigns = combine3 exp_in_tys f_args exp_es
                  |> add_offsets3
                  |> List.map (fun (x,y,z) -> (x, Some y, z)) in

    let state = List.fold_left (fun state (in_ty, mvar, e) ->
        abs_assign state in_ty mvar e)
        state assigns in

    let assign_vars = List.map (fun (_,x,_) -> oget x) assigns in

    (assign_vars,state)

  let forget_f_vars f state =
    let f_decl = get_fun_def state.prog f |> oget in
    let f_vs =  fun_args f_decl
               @ fun_locals f_decl in

    (* We forget f variables *)
    let abs = AbsDom.forget_list state.abs f_vs in

    (* We uninitialize f variables *)
    let f_as = List.fold_left (fun acc v -> match v with
        | Mvalue a -> a :: acc
        | _ -> acc ) [] f_vs in
    let abs = AbsDom.clear_init abs f_as in

    { state with abs = abs }

  (* Forget the values of all variables with can be modified by side-effect
     during a function call. *)
  let forget_side_effect state =
    let vs_mem = List.map (fun x ->
        MmemRange x) (AbsDom.top_mem_loc state.abs) in
    let vs_globs = prog_globals state.env in

    {state with abs = AbsDom.forget_list state.abs (vs_mem @ vs_globs) }

  (* Prepare a function call. Returns the state where:
     - The arguments of f have been evaluated.
     - The variables of f have been un-initialized and forgotten,
     except for arguments. *)
  let prepare_call state f es =
    let state = forget_f_vars f state in
    let (assign_vars,state) = aeval_f_args state f es in
    (* We know that the arguments of f are initialized. *)
    init_args assign_vars state


  let return_call state f lvs =
    let f_decl = get_fun_def state.prog f |> oget in

    let f_map (x,y) = match y with
      | None -> [x,None]
      | Some u ->
        let eu = expand_arr_vars [u] in
        List.map (fun z -> (x, Some z)) eu in

    let f_rets_no_offsets = fun_rets_no_offsets f_decl
    and out_tys = f_decl.f_tyout |> expand_arr_tys
    and mlvs = List.map (fun x -> (x,mvar_of_lvar state.abs x)) lvs
               |> List.map f_map
               |> List.flatten in

    let rec add_offsets_lv assigns = match assigns with
      | [] -> []
      | (ty, Mvalue (Avar v),(lvty, Some (Mvalue (Avar vr)))) :: tail ->
        (ty, Mvalue (Avar v),(lvty, Some (Mvalue (Avar vr))))
        :: (ty, MvarOffset v,(lvty, Some (MvarOffset vr)))
        :: add_offsets_lv tail
      | u :: tail -> u :: add_offsets_lv tail in

    let ret_assigns = combine3 out_tys f_rets_no_offsets mlvs
                      |> add_offsets_lv in

    (* Finally, we assign the returned values in the corresponding lvalues *)
    let abs = List.fold_left (fun abs (out_ty,rvar,(lv,mlvo)) ->
        match mlvo with
        | None -> abs
        | Some mlv -> match ty_mvar mlv with
          | Bty Bool ->
            let smlv = string_of_mvar mlv in
            let rconstr = BVar (string_of_mvar rvar, true) in
            AbsDom.assign_bexpr abs smlv rconstr

          | _ ->
            let apr_env = AbsDom.get_env abs in
            let mret = Mtexpr.var apr_env rvar in

            (* let lv_size = wsize_of_ty (ty_lval lv) *)
            let lv_size = wsize_of_ty (ty_lval lv)
            and ret_size = wsize_of_ty out_ty in

            (* Numerical abstraction *)
            let expr = match ty_mvar mlv, ty_mvar rvar with
              | Bty Int, Bty Int -> mret
              | Bty (U _), Bty Int ->
                (* TODO: Signed *)
                wrap_if_overflow abs mret Unsigned lv_size
              | Bty (U _), Bty (U _) ->
                cast_if_overflows abs lv_size ret_size mret
              | _, _ -> assert false in

            let s_expr = sexpr_from_simple_expr expr in
            let abs = AbsDom.assign_sexpr abs mlv s_expr in

            (* Points-to abstraction *)
            let pt_expr = PtVars [rvar] in
            AbsDom.assign_pt_expr abs mlv pt_expr)
        state.abs ret_assigns in

    (* We forget the variables of f to get a smaller abstract element,
       and we know that variables in in lvs are initialized *)
    { state with abs = abs }
    |> forget_f_vars f
    |> init_lvs lvs

  let split_opn n opn es = match opn with
    | E.Oset0 ws -> [None;None;None;None;None;
                     Some (Pcast (ws, Pconst (B.of_int 0)))]

    | E.Ox86_CMP ws ->
      (* Input types: ws, ws *)
      (* Return flags in order: of, cf, sf, ?, zf *)
      let el,er = match es with [el;er] -> el,er | _ -> assert false in
      let of_f = None
      and cf = None
      and sf = None
      and unknown = None
      and zf = Some (Papp2 (E.Oeq (E.Op_w ws),
                            Papp2 (E.Osub (E.Op_w ws),
                                   el,
                                   er),
                            Pconst (B.of_int 0))) in
      [of_f;cf;sf;unknown;zf]

    | _ -> List.init n (fun _ -> None)


  (* Abstract evaluation of an assignment *)
  let abs_lvassign : astate -> 'a gty glval -> ty gexpr -> astate =
    fun state lv e ->
      abs_assign state (ty_lval lv) (mvar_of_lvar state.abs lv) e

  let num_instr_evaluated = ref 0

  let rec aeval_ginstr : ('ty,'info) ginstr -> astate -> astate =
    fun ginstr state ->
      debug (fun () ->
          Format.eprintf "@[<v>@[<v>%a@]@;%d Instr: %a %a@;@]%!"
            (AbsDom.print ~full:true) state.abs
            (let a = !num_instr_evaluated in incr num_instr_evaluated; a)
            L.pp_sloc (fst ginstr.i_loc)
            (Printer.pp_instr ~debug:false) ginstr) ;

      (* We stop if the abstract state is bottom *)
      if AbsDom.is_bottom state.abs then state
      else
        (* We check the safety conditions *)
        let conds = safe_instr ginstr in
        let state = check_safety state conds in

        match ginstr.i_desc with
        | Cassgn (lv, _, _, e) ->
          abs_assign state (ty_lval lv) (mvar_of_lvar state.abs lv) e
          |> init_lv lv

        | Copn (lvs,_,opn,es) ->
          let assgns = split_opn (List.length lvs) opn es in
          let state, mlvs_forget =
            List.fold_left2 (fun (state, mlvs_forget) lv e_opt ->
                match mvar_of_lvar state.abs lv, e_opt with
                | None,_ ->
                  (* TODO: This is unsound for flags, which are always set. *)
                  (state, mlvs_forget)
                | Some mlv, None -> (state, mlv :: mlvs_forget)
                | Some mlv, Some e ->
                  (abs_assign state (ty_lval lv) (Some mlv) e, mlvs_forget))
              (state,[]) lvs assgns in

          { state with abs = AbsDom.forget_list state.abs mlvs_forget }
          |> init_lvs lvs

        | Cif(e,c1,c2) ->
          let eval_branch state oec c =
            let state = match oec with
              | Some ec ->
                let () = debug (fun () ->
                    Format.eprintf "@[<v>Branch: meet with %a@;@]"
                      pp_btcons ec) in
                { state with
                  abs = AbsDom.meet_btcons state.abs ec }

              | None ->
                let () = debug (fun () ->
                    Format.eprintf "@[<v>Branch: no meet@;@]") in
                state in

            aeval_gstmt c state in

          (* We abstractly evaluate the left branch *)
          let oec = bexpr_to_btcons e state.abs in
          let lstate = eval_branch state oec c1 in

          (* We abstractly evaluate the right branch
             Be careful the start from lstate, as we need to use the
             updated abstract iterator. *)
          let noec = obind flip_btcons oec in
          let rstate = eval_branch { lstate with abs = state.abs } noec c2 in

          Format.eprintf "@[<v>If join %a for Instr:@;%a @;\
                          Of:@;%a@;And:@;%a@;@]%!"
            L.pp_sloc (fst ginstr.i_loc)
            (Printer.pp_instr ~debug:false) ginstr
            (AbsDom.print ~full:true) lstate.abs
            (AbsDom.print ~full:true) rstate.abs;
          (* Finally, we compute the join of the two branches *)
          { rstate with abs = AbsDom.join lstate.abs rstate.abs }

        | Cwhile(c1, e, c2) ->
          let cpt = ref 0 in
          let state = aeval_gstmt c1 state in

          (* We now check that e is safe *)
          let conds = safe_e e in
          let state = check_safety state conds in

          let oec = bexpr_to_btcons e state.abs in

          (* Unroll one time the loop. *)
          let unroll_once state =
            let () = debug (fun () -> Format.eprintf "Loop %d@;" !cpt) in
            cpt := !cpt + 1;
            (* We enter the loop, hence 'e' abstractly evaluates to true *)
            let state_i = match oec with
              | Some ec -> { state with abs = AbsDom.meet_btcons state.abs ec }
              | None -> state in

            (* We evaluate the while loop body *)
            let state_o = aeval_gstmt (c2 @ c1) state_i in
            Format.eprintf "@[<v 2>Join of:@;%a@;And (join):@;%a@;@]%!"
              (AbsDom.print ~full:true) state.abs
              (AbsDom.print ~full:true) state_o.abs;
            (* We compute the join with the initial abstract state *)
            { state_o with abs = AbsDom.join state.abs state_o.abs } in

          let rec unroll_times i state pre_state =
            if i = 0 then (state,pre_state)
            else unroll_times (i - 1) (unroll_once state) (Some state) in

          let rec stabilize state pre_state =
            if (pre_state <> None) &&
               (AbsDom.is_included state.abs (oget pre_state).abs) then begin
              let () = debug (fun () -> Format.eprintf "Exit loop@;") in
              (state,None) end
            else
              let state' = unroll_once state in
              Format.eprintf "@[<v 2>Widening of:@;%a@;And (widening):@;%a@;@]%!"
                (AbsDom.print ~full:true) state.abs
                (AbsDom.print ~full:true) state'.abs;
              let w_abs = AbsDom.widening state.abs state'.abs in
              stabilize { state' with abs = w_abs } (Some state) in

          (* We first unroll the loop k_unroll times. We then stabilize the
             abstraction (in finite time) using AbsDom.widening.
             (k_unroll is a parameter of the analysis). *)
          let (state,pre_state) = unroll_times k_unroll state None in
          let (state,_) = stabilize state pre_state in

          (* Finally, we meet the state with the negation of the
             loop condition. *)
          begin match obind flip_btcons oec with
            | Some neg_ec ->
              { state with abs = AbsDom.meet_btcons state.abs neg_ec }
            | None -> state end

        | Ccall(_, lvs, f, es) ->
          let f_decl = get_fun_def state.prog f |> oget in
          let fn = f_decl.f_name in

          debug (fun () -> Format.eprintf "@[<v>Call %s:@;@]" fn.fn_name);

          let state = match abs_call_strategy with
            | CallDirect -> aeval_call f es state

            | CallWidening ->
              let callsite,_ = ginstr.i_loc in
              aeval_call_widening f es callsite state in

          (* We check the safety conditions of the return *)
          let conds = safe_return f_decl in
          let state = check_safety state conds in

          let () = debug (fun () ->
              Format.eprintf "@[<v>@[<v>%a@]Returning %s:@;@]%!"
                (AbsDom.print ~full:false) state.abs fn.fn_name) in

          return_call state f lvs

        | Cfor(i, (d,e1,e2), c) ->
          match aeval_cst_int state.abs e1, aeval_cst_int state.abs e2 with
          | Some z1, Some z2 ->
            if z1 = z2 then state else
              let init_i, final_i, op = match d with
                | UpTo -> assert (z1 < z2); (z1, z2 - 1, fun x -> x + 1)
                | DownTo -> assert (z1 < z2); (z2, z1 + 1, fun x -> x - 1) in

              let rec mk_range i f op =
                if i = f then [i] else i :: mk_range (op i) f op in

              let range = mk_range init_i final_i op
              and mvari = Mvalue (Avar (L.unloc i))
              and apr_env = AbsDom.get_env state.abs in

              List.fold_left ( fun state ci ->
                  (* We set the integer variable i to ci. *)
                  let expr_ci = Mtexpr.cst apr_env (Coeff.s_of_int ci)
                                |> sexpr_from_simple_expr in
                  let abs' = AbsDom.assign_sexpr state.abs mvari expr_ci in
                  let abs' = AbsDom.is_init abs' (Avar (L.unloc i)) in
                  let state' = { state with abs = abs' } in

                  (* We evaluate the loop body *)
                  aeval_gstmt c state')
                state range

          | _ ->
            Format.eprintf "@[<v>For loop: \
                            I was expecting a constant integer expression.@;\
                            Expr1:@[%a@]@;Expr2:@[%a@]@;@."
              (Printer.pp_expr ~debug:true) e1
              (Printer.pp_expr ~debug:true) e2;
            assert false

  and aeval_call : funname -> 'a gty gexprs -> astate -> astate =
    fun f es state ->
      let f_decl = get_fun_def state.prog f |> oget in
      prepare_call state f es |> aeval_gstmt f_decl.f_body

  and aeval_call_widening : funname -> 'a gty gexprs -> L.t -> astate -> astate =
    fun f es callsite state ->
      let itk = ItFunIn (f,callsite) in
      if ItMap.mem itk state.it then
        (* f has been abstractly evaluated before *)
        let (in_abs,out_abs) = ItMap.find itk state.it in
        if AbsDom.is_included state.abs in_abs then
          (* We meet with f output over-abstraction, taking care of
             forgetting all variables that may be modified through side
             effects during f evaluation *)
          let state = forget_side_effect state in
          { state with abs = AbsDom.meet state.abs out_abs }
        else
          (* We do a widening to accelerate convergence *)
          let n_in_abs =
            AbsDom.widening in_abs (AbsDom.join in_abs state.abs) in
          let state = { state with abs = n_in_abs }
                      |> aeval_call f es in
          { state with
            it = ItMap.add itk (n_in_abs,state.abs) state.it }

      else
        (* We abstractly evaluate f for the first time *)
        let in_abs = state.abs in
        let state = aeval_call f es state in
        { state with it = ItMap.add itk (in_abs,state.abs) state.it }

  and aeval_gstmt : ('ty,'i) gstmt -> astate -> astate =
    fun gstmt state ->
      let state = List.fold_left (fun state ginstr ->
          aeval_ginstr ginstr state)
          state gstmt in
      let () = debug (fun () ->
          if gstmt <> [] then
            Format.eprintf "%a%!"
              (AbsDom.print ~full:false) state.abs) in
      state


  let print_mem_ranges state f_decl =
    let in_vars = fun_in_args_no_offset f_decl
                  |> List.map otolist |> List.flatten in
    let vars_to_keep = in_vars @ get_mem_range state.env in
    let vars = in_vars @ fun_vars f_decl state.env in
    let rem_vars = List.fold_left (fun acc v ->
        if (List.mem v vars_to_keep) then acc else v :: acc )
        [] vars in

    let abs_proj = AbsDom.forget_list state.abs rem_vars in
    Format.eprintf "@[<v 0>Final offsets full abstract value:@;@[%a@]@]@."
      (AbsDom.print ~full:true) state.abs;
    Format.eprintf "@[<v 0>Final offsets:@;@[%a@]@]@."
      (AbsDom.print ~full:true) abs_proj


  let analyze : unit Prog.func -> unit Prog.prog -> bool =
    fun main_decl prog ->
      (* Stats *)
      let exception Done in

      let t_start = Sys.time () in
      let print_stats _ =
        Format.eprintf "@[<v 0>Duration: %1f@;%a@]@."
          (Sys.time () -. t_start)
          Prof.print () in

      (* We print stats before exciting *)
      let hndl = Sys.Signal_handle (fun _ -> print_stats (); raise Done) in
      let old_handler = Sys.signal Sys.sigint hndl in

      (* We ensure that all variable names are unique *)
      let main_decl,prog = MkUniq.mk_uniq main_decl prog in
      let state = init_state main_decl prog in

      try
        let m_fn = main_decl.f_name.fn_name in
        let () = Format.eprintf "@[<v>Analyzing function %s@;@]@." m_fn in

        (* We abstractly evaluate the main function *)
        let final_st = aeval_gstmt main_decl.f_body state in

        (* We check the safety conditions of the return *)
        let conds = safe_return main_decl in
        let final_st = check_safety final_st conds in

        print_mem_ranges final_st main_decl;

        (* TODO:temp. *)
        (* assert (not final_st.violation); *)

        let () = debug (fun () -> print_stats ()) in
        let () = Sys.set_signal Sys.sigint old_handler in

        not final_st.violation
      with
      | Manager.Error exclog as e ->
        Printexc.print_backtrace stderr;
        Format.eprintf "@[<v>Apron Error Message:@;@[%a@]@;@]"
          Manager.print_exclog exclog;
        raise e
end
