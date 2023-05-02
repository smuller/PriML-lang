signature PSETCSTRS = 
sig
    exception PSConstraints of string

    (* process unified priority set constraints *)
    val add_unified_pscstrs : IL.psconstraint list -> unit
    val ret_unified_pscstrs : unit -> IL.psconstraint list
    val clear_unified_pscstrs : unit -> unit
    
    (* add priority set constraint *)
    val pscstr_eq   : IL.prioset -> IL.prioset -> IL.psconstraint list
    val pscstr_sup  : IL.prioset -> IL.prioset -> IL.psconstraint list
    val pscstr_cons : IL.prioset -> IL.prioset -> IL.psconstraint list
    val pscstr_gen  : IL.prioset -> IL.prioset -> IL.prioset -> 
                        IL.psconstraint list

    (* solve system of priority set constraints *)
    val solve_pscstrs : PSContext.pscontext -> IL.psconstraint list -> PSContext.pscontext

    (* check psconstraints in the solved system *)
    val check_pscstrs_sol : Context.context -> PSContext.pscontext ->
                              IL.psconstraint list -> unit

    (* print function *)
    val print_pscstrs : IL.psconstraint list -> unit
    val print_psctx : PSContext.pscontext -> unit
end
