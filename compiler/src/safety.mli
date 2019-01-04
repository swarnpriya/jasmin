
module type ProgWrap = sig
  val main : unit Prog.func
  val prog : unit Prog.prog
end

(* Abstract Interpreter.
   TODO: some unprecision
   - signed operations are unsoundly implemented
   - almost all n-ary operations are over-approximated by top
   - memory read always return top *)
module AbsInterpreter (PW : ProgWrap) : sig
  val analyze : unit -> bool
end
