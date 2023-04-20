signature PSETCSTRS = 
sig
    exception PSConstraints of string

    (* clear all priority set constraints *)
    val clear_psconstraints : unit -> unit
    
    (* add priority set constraint *)
    val pscstr_eq : IL.prioset -> IL.prioset -> unit
    val pscstr_sup : IL.prioset -> IL.prioset -> unit
    val pscstr_cons : IL.prioset -> IL.prioset -> unit
    val pscstr_gen : IL.prioset -> IL.prioset -> IL.prioset -> unit

    (* solve system of priority set constraints *)
    val solve_pscstrs : PSContext.pscontext -> PSContext.pscontext

    (* check psconstraints in the solved system *)
    val check_pscstrs_sol : Context.context -> PSContext.pscontext -> unit
end
