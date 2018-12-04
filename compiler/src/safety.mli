module type AbsNumBoolType

module AbsDom : AbsNumBoolType

(* Abstract Interpreter.
   TODO: some unprecision
   - signed operations are unsoundly implemented
   - almost all n-ary operations are over-approximated by top
   - memory read always return top *)
module AbsInterpreter (AbsDom : AbsNumBoolType) : sig
  val analyze : unit Prog.func -> unit Prog.prog -> bool
end
