
structure PSetCstrs :> PSETCSTRS = 
struct

    open IL  
    open PSContext

    exception PSConstraints of string

    val all_psconstraints = ref (nil : psconstraint list)

    fun add_psconstraint pscstr = 
      let in 
        all_psconstraints := pscstr :: !all_psconstraints;
        ()
      end

    (* initialize priority set variables in context *)
    fun psctx_init (psevars: prioset list) = 
      let 
        fun init_fold (PSSet _, ctx) = raise (PSConstraints "cannot have set constant as key")
          | init_fold (psevar, ctx) =
            (case (PSEvarMap.find (ctx, psevar)) of 
              NONE => PSEvarMap.insert (ctx, psevar, PrioSet.empty)
            | _ => ctx)
      in
        List.foldl init_fold PSEvarMap.empty psevars
      end

    (* priority set constraints solver *)
    fun psconstraints_solver (psctx: pscontext) (psconstraints: psconstraint list)= 
      let 
        fun check_sup_constraint (s1, s2) = PrioSet.equal (PrioSet.difference (s1, s2), PrioSet.empty)

        fun solver_fold (constraint, psctx) = 
          case constraint of 
            PSCons _ => psctx
          | PSSup (PSSet _, _) => raise (PSConstraints "set constant cannot be a superset in the constraint")
          | PSSup (ps as PSEvar _, PSSet s) => 
              (case PSEvarMap.find (psctx, ps) of 
                NONE => raise (PSConstraints "cannot find psevar in context")   (* this error shouldn't be raised *)
              | SOME s' => 
                  if check_sup_constraint (s', s) then psctx 
                  else PSEvarMap.insert (psctx, ps, PrioSet.union (s', s)))
          | PSSup (ps1 as PSEvar _, ps2 as PSEvar _) =>
              (case (PSEvarMap.find (psctx, ps1), PSEvarMap.find (psctx, ps2)) of 
                (SOME s1, SOME s2) => 
                  if check_sup_constraint (s1, s2) then psctx
                  else PSEvarMap.insert (psctx, ps1, PrioSet.union (s1, s2))
              | _ => raise (PSConstraints "cannot find psevar in context"))   (* this error shouldn't be raised *)
      in 
        let val psctx' = List.foldl solver_fold psctx (!all_psconstraints)
        in
          if PSEvarMap.collate PrioSet.compare (psctx', psctx) = EQUAL then psctx'
          else psconstraints_solver psctx' (!all_psconstraints)
        end
      end

    (* check (Sync) PSCons constraints in solved system *)
    fun check_psconstraints (ctx: Context.context) (psctx: pscontext) = 
    let 
      (* check if sets are not empty and satisfy (Sync) PSCons constraints *)
      fun check_sets (s1, s2) = 
        if PrioSet.isEmpty s1 orelse PrioSet.isEmpty s2 then raise (PSConstraints "empty priority set")
        else 
          PrioSet.app 
            (fn p => 
              PrioSet.app 
                (fn p' => if Context.checkcons ctx p p' then () else raise (PSConstraints "constraint violated")) 
                s2) 
            s1

      (* helper function to check set constraint *)
      fun check_app (PSSup _) = ()
        | check_app (PSCons (PSSet s, ps as PSEvar _)) = 
            (case PSEvarMap.find (psctx, ps) of
              SOME s' => check_sets (s, s')
            | _ => raise (PSConstraints "cannot find psevar in context"))   (* this error shouldn't be raised *)
        | check_app (PSCons (ps1 as PSEvar _, ps2 as PSEvar _)) = 
            (case (PSEvarMap.find (psctx, ps1), PSEvarMap.find (psctx, ps2)) of 
              (SOME s, SOME s') => check_sets (s, s')
            | _ => raise (PSConstraints "cannot find psevar in context"))   (* this error shouldn't be raised *)
        | check_app (PSCons (ps as PSEvar _, PSSet s')) = 
            (case PSEvarMap.find (psctx, ps) of 
              SOME s => check_sets (s, s')
            | _ => raise (PSConstraints "cannot find psevar in context"))   (* this error shouldn't be raised *)
    in 
      List.app check_app (!all_psconstraints)
    end

end
