(* -------------------------------------------------------------------- *)
open Wsize
open Global
open Prog

type 'info coq_tbl

val string0_of_string : string -> 'a (* coq string *)
val string_of_string0 : 'a (* coq string *) -> string

val bi_of_nat : Datatypes.nat -> Bigint.zint
val int_of_nat : Datatypes.nat -> int

val pos_of_int : int -> BinNums.positive
val z_of_int   : int -> BinNums.coq_Z
val int_of_pos : BinNums.positive -> int
val bi_of_z    : BinNums.coq_Z -> B.zint

val pos_of_bi : Bigint.zint -> BinNums.positive
val bi_of_pos : BinNums.positive -> Bigint.zint

val z_of_bi : Bigint.zint -> BinNums.coq_Z
val bi_of_z : BinNums.coq_Z -> Bigint.zint

val int64_of_bi : Bigint.zint -> Obj.t
val bi_of_int256 : Obj.t -> Bigint.zint
val bi_of_int128 : Obj.t -> Bigint.zint
val bi_of_int64 : Obj.t -> Bigint.zint
val bi_of_int32 : Obj.t -> Bigint.zint
val bi_of_int16 : Obj.t -> Bigint.zint
val bi_of_int8 : Obj.t -> Bigint.zint
val bi_of_word : wsize -> Obj.t -> Bigint.zint

(* -------------------------------------------------------------------- *)
val cty_of_ty : Prog.ty -> Type.stype
val ty_of_cty : Type.stype -> Prog.ty
(* -------------------------------------------------------------------- *)
val cvar_of_var : 'a coq_tbl -> var -> Var0.Var.var
val var_of_cvar : 'a coq_tbl -> Var0.Var.var -> var
val vari_of_cvari : 'a coq_tbl -> Expr.var_i -> var L.located

val lval_of_clval : 'a coq_tbl -> Expr.lval -> Prog.lval

val global_of_cglobal : global -> wsize * Name.t

val cexpr_of_expr : 'info coq_tbl -> expr -> Expr.pexpr
val expr_of_cexpr : 'info coq_tbl -> Expr.pexpr -> expr

val cfun_of_fun : 'info coq_tbl -> funname -> BinNums.positive
val fun_of_cfun : 'info coq_tbl -> BinNums.positive -> funname

val gd_of_cgd : global * BinNums.coq_Z -> wsize * Name.t * B.zint
val get_iinfo   : 'info coq_tbl -> BinNums.positive -> (L.t * L.t list) * 'info

val cfdef_of_fdef : 'info coq_tbl -> 'info func -> BinNums.positive * Expr.fundef
val fdef_of_cfdef : 'info coq_tbl -> BinNums.positive * Expr.fundef -> 'info func

val cprog_of_prog : var list -> 'info -> 'info prog -> 'info coq_tbl * Expr.prog
val prog_of_cprog : 'info coq_tbl -> Expr.prog -> 'info prog

val fresh_cvar : 'info coq_tbl -> string -> ty -> Var0.Var.var
