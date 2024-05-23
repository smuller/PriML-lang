
signature UNIFY =
sig
    exception Unify of string

    val global_cstrs : PSetCstrs.psconstraint list ref

    val new_evar : unit -> IL.typ
    val new_pevar : unit -> IL.prio
    val new_psevar : unit -> IL.prioset

    val get_psevars : unit -> IL.prioset list
    (* reset the list of evars *)
    val clear_evars : unit -> unit
    (* set all unset evars to unit/home *)
    val finalize_evars : unit -> unit

    val new_ebind : unit -> 'a IL.ebind ref

    val unify  : Context.context -> IL.typ -> IL.typ -> unit

    (* val supertype  : Context.context -> IL.typ -> IL.typ -> unit *)

    (* val unifyp : Context.context -> IL.prio -> IL.prio -> unit *)

end
