
signature PATTERN =
sig

    exception Pattern of string

    (* elaborate user elab elabt elabw ctx world loc (ob,arms,def) 
       ob: must be variables

       returns elaborated pattern match and its type
       *)
    val elaborate : bool -> (Context.context -> EL.exp -> IL.exp * IL.typ) ->
        (* elabt *)
        (Context.context -> Pos.pos -> EL.typ -> IL.typ) ->
        (* elabw *)
        (* (Context.context -> Pos.pos -> string -> IL.world) -> *)
        Context.context -> (* IL.world -> *) EL.node_info ->
                           string list * 
                           (EL.pat list * EL.exp) list * 
                           (unit -> EL.exp) -> 
        IL.exp * IL.typ

end
