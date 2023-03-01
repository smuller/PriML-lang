signature PSETCSTRS = 
sig
    exception PSetConstraints of string
    
    (* initialize priority set context *)
    val psctx_init : prioset list -> IL.PrioSet.set PSEvarMap.map

    (* solve system of priority set constraints *)
    val psconstraints_solver : pscontext -> psconstraint list -> pscontext

    (* check psconstraints in the solved system *)
    fun check_psconstraint : Context.context -> pscontext -> pscontraint list -> unit
end
