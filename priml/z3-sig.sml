signature PRIMLZ3 =
sig
    type z3 = string
    val setup : Context.context -> z3
    val of_constraint : IL.prio * IL.prio -> z3
    val negate_constraint : IL.prio * IL.prio -> z3
    val negate_and_constraints : (IL.prio * IL.prio) list -> z3
    val compose : z3 * z3 -> z3
    val check : z3 -> bool
end
