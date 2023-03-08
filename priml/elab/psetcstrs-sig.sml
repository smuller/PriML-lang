signature PSETCSTRS = 
sig
    exception PSConstraints of string
    
    (* add priority set constraint *)
    val add_psconstraint : IL.psconstraint -> unit

    (* initialize priority set context *)
    val psctx_init : IL.prioset list -> PSContext.pscontext

    (* solve system of priority set constraints *)
    val psconstraints_solver : PSContext.pscontext -> IL.psconstraint list -> PSContext.pscontext

    (* check psconstraints in the solved system *)
    val check_psconstraints : Context.context -> PSContext.pscontext -> unit
end
