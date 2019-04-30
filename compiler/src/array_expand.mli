open Prog

val vstack : var

val arrexp_func : 'info func -> 'info func

val stk_alloc_func : 'info func -> (var * int) list * int 

val init_glob : 'info prog -> 
      Ssralg.GRing.ComRing.sort list * Prog.var * (Prog.var * int) list
