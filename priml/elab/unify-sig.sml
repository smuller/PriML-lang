
signature UNIFY =
sig
    exception Unify of string

    val global_cstrs : IL.psconstraint list ref

    val new_ebind : unit -> 'a IL.ebind ref

    val unify  : Context.context -> IL.typ -> IL.typ -> unit

    val supertype  : Context.context -> IL.typ -> IL.typ -> unit

    (* val unifyp : Context.context -> IL.prio -> IL.prio -> unit *)

end
