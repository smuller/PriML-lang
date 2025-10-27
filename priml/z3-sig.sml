signature PRIMLZ3 =
sig
    type z3 = string
    val setup : string option -> Context.context -> Variable.var list -> z3
    val of_constraint : IL.prio * IL.prio -> z3
    val negate_constraint : IL.prio * IL.prio -> z3
    val negate_and_constraints : (IL.prio * IL.prio) list -> z3
    val compose : z3 * z3 -> z3
    val check : z3 -> bool
    val comment : string -> z3

    val z3calls : int ref
    val z3time : LargeInt.int ref
end
