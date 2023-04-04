
signature UNIFY =
sig
    exception Unify of string

    val new_ebind : unit -> 'a IL.ebind ref

    val unify  : Context.context -> IL.typ -> IL.typ -> unit

    val unifyp : Context.context -> IL.prio -> IL.prio -> unit

    val unifyps : IL.prioset -> IL.prioset -> unit

end
