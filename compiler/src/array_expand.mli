open Prog

val vstack : var

val arrexp_func : 'info func -> 'info func

val stk_alloc_func : 
  'info func -> (var * int) list * int * Sv.t * [> `InReg of var | `InStack of int ] option
