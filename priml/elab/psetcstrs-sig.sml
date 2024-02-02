signature PSETCSTRS = 
sig
    exception PSConstraints of string

    type pscontext = IL.PrioSet.set IntMap.map

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
    val solve_pscstrs : pscontext -> psconstraint list -> pscontext

    (* check psconstraints in the solved system *)
    val check_pscstrs_sol : pscontext ->  psconstraint list -> unit
(*
    val dosub_cstr : psconstraint -> psconstraint
    val dosub : IL.prioset -> IL.prioset
*)
end
