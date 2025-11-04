signature PRIMLZ3 =
sig
    type z3
    val setup : string option -> Context.context -> Variable.var list -> z3
    val add_constraint : z3 * (IL.prio * IL.prio) -> z3
    val add_negated_constraint : z3 * (IL.prio * IL.prio) -> z3
    val add_negate_and_constraints : z3 * (IL.prio * IL.prio) list -> z3
    val check : z3 -> bool
    val add_comment : z3 * string -> z3

    val z3calls : int ref
    val z3time : LargeInt.int ref
end
