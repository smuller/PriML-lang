
structure PrioSetConstraints :> PSETCSTRS = 
struct

    open IL  

    exception PSetConstraints of string

    (* NOTE: the key for PSEvarMap should only be PSEvar.
        There should be an error otherwise. *)
    fun compare (PSEvar _, PSSet _) = GREATER
      | compare (PSSet _, PSEvar _) = LESS
      | compare (PSSet s1, PSSet s2) = PrioSet.compare (s1, s2)
      | compare (PSEvar (ref (Bound _)), PSEvar (ref (Free _))) = GREATER
      | compare (PSEvar (ref (Free _)), PSEvar (ref (Bound _))) = LESS
      | compare (PSEvar (ref (Free n1)), PSEvar (ref (Free n2))) = Int.compare (n1, n2)
      | compare (PSEvar (ref (Bound w1)), PSEvar (ref (Bound w2))) = compare (w1, w2)

    structure PSEvarMap = SplayMapFn (struct
                                        type ord_key = prioset
                                        val compare = compare
                                      end)

    datatype pscontext = PrioSet.set PSEvarMap.map

    (* priority set constraint
        PSSup (ps1, ps2): ps1 is a super set of ps2
        PSCons (ps1, ps2): priorities in ps1 is less than or equal to priorities in ps2  *)
    datatype psconstraint =
      PSSup of prioset * prioset
    | PSCons of prioset * prioset 

    (* initialize priority set variables in context *)
    fun psctx_init (psevars: prioset list) = 
      let 
        fun init_fold (PSSet _, ctx) = raise (PSetConstraints "cannot have set constant as key")
          | init_fold (psevar, ctx) =
            (case (PSEvarMap.find (ctx, psevar)) of 
              NONE => PSEvarMap.insert (ctx, psevar, PrioSet.empty)
            | _ => ctx)
      in
        List.foldl init_fold PSEvarMap.empty psevars
      end

    (* priority set constraints solver *)
    fun psconstraints_solver (psctx: pscontext) (constraints: psconstraint list) = 
      let 
        fun check_sup_constraint (s1, s2) = PrioSet.equal (PrioSet.difference (s1, s2), PrioSet.empty)

        fun solver_fold (constraint, psctx) = 
          case constraint of 
            PSCons _ => psctx
          | PSSup (PSSet _, _) => raise (PSetConstraints "set constant cannot be a superset in the constraint")
          | PSSup (ps as PSEvar _, PSSet s) => 
              (case PSEvarMap.find (psctx, ps) of 
                NONE => raise (PSetConstraints "cannot find psevar in context")   (* this error shouldn't be raised *)
              | SOME s' => 
                  if check_sup_constraint (s', s) then psctx 
                  else PSEvarMap.insert (psctx, ps, PrioSet.union (s', s)))
          | PSSup (ps1 as PSEvar _, ps2 as PSEvar _) =>
              (case (PSEvarMap.find (psctx, ps1), PSEvarMap.find (psctx, ps2)) of 
                (SOME s1, SOME s2) => 
                  if check_sup_constraint (s1, s2) then psctx
                  else PSEvarMap.insert (psctx, ps1, PrioSet.union (s1, s2))
              | _ => raise (PSetConstraints "cannot find psevar in context"))   (* this error shouldn't be raised *)
      in 
        let val psctx' = List.foldl solver_fold psctx constraints
        in
          if PSEvarMap.collate PrioSet.compare (psctx', psctx) = EQUAL then psctx'
          else psconstraints_solver psctx' constraints
        end
      end

    (* check (Sync) PSCons constraints in solved system *)
    fun check_psconstraint (ctx: Context.context) (psctx: pscontext) (constraints: psconstraint list) = 
    let 
      (* check if sets are not empty and satisfy (Sync) PSCons constraints *)
      fun check_sets (s1, s2) = 
        if PrioSet.isEmpty s1 orelse PrioSet.isEmpty s2 then raise (PSetConstraints "empty priority set")
        else 
          PrioSet.app 
            (fn p => 
              PrioSet.app 
                (fn p' => if Context.checkcons ctx p p' then () else raise (PSetConstraints "constraint violated")) 
                s2) 
            s1

      (* helper function to check set constraint *)
      fun check_app (PSSup _) = ()
        | check_app (PSCons (PSSet s, ps as PSEvar _)) = 
            (case PSEvarMap.find (psctx, ps) of
              SOME s' => check_sets (s, s')
            | _ => raise (PSetConstraints "cannot find psevar in context"))   (* this error shouldn't be raised *)
        | check_app (PSCons (ps1 as PSEvar _, ps2 as PSEvar _)) = 
            (case (PSEvarMap.find (psctx, ps1), PSEvarMap.find (psctx, ps2)) of 
              (SOME s, SOME s') => check_sets (s, s')
            | _ => raise (PSetConstraints "cannot find psevar in context"))   (* this error shouldn't be raised *)
        | check_app (PSCons (ps as PSEvar _, PSSet s')) = 
            (case PSEvarMap.find (psctx, ps) of 
              SOME s => check_sets (s, s')
            | _ => raise (PSetConstraints "cannot find psevar in context"))   (* this error shouldn't be raised *)
    in 
      List.app check_app constraints
    end

end
