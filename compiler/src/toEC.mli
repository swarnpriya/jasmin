val ty_expr : Prog.ty Prog.gexpr -> Type.stype
val ty_lval : 'a Prog.gty Prog.glval -> 'a Prog.gty
val extract : Format.formatter ->
        Utils.model -> 'a Prog.prog -> string list -> unit
