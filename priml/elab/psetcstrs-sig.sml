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

    val new_prioset : unit -> IL.prioset
    val new_rvar : unit -> IL.rfmt

    type assign = (Variable.var * IL.pconstraint list) IntMap.map
    exception Unsolvable of psconstraint

    val string_of_assign : assign -> string
    val string_of_pconstraint : assign option -> psconstraint -> string

    val check_wf : assign -> Context.context -> IL.prioset -> bool
    val check_cons : assign -> Context.context -> IL.prioset * IL.prioset -> bool
    val check_sub : assign -> Context.context -> IL.prioset * IL.prioset -> bool
    val check : assign -> psconstraint -> bool
    val weaken_wf : assign -> Context.context -> IL.prioset -> assign option
    val weaken_sub : assign -> Context.context -> IL.prioset * IL.prioset -> (int * assign) option

end
