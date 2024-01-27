signature PSETCSTRS = 
sig
    exception PSConstraints of string

    datatype psconstraint = 
      PSSup of Context.context * IL.prioset * IL.prioset 
    | PSCons of Context.context * IL.prioset * IL.prioset
    | PSWellformed of Context.context * IL.prioset

    val psctol : psconstraint  -> Layout.layout

    (* add priority set constraint *)
    val pscstr_eq   : Context.context -> IL.prioset -> IL.prioset -> psconstraint list
    val pscstr_sup  : Context.context -> IL.prioset -> IL.prioset -> psconstraint list
    val pscstr_cons : Context.context -> IL.prioset -> IL.prioset -> psconstraint list
    val pscstr_gen  : Context.context -> IL.prioset -> IL.prioset -> IL.prioset -> 
                      psconstraint list

    val pscstr_wf   : Context.context -> IL.prioset -> psconstraint list

    (* solve system of priority set constraints *)
    val solve_pscstrs : PSContext.pscontext -> psconstraint list -> PSContext.pscontext

    (* check psconstraints in the solved system *)
    val check_pscstrs_sol : PSContext.pscontext ->  psconstraint list -> unit
end
