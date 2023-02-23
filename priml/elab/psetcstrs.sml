
structure PrioSetConstraints :> PSETCSTRS = 
struct

    open IL  

    exception PSetConstraints of String

    (* NOTE: the key for PSEvarMap should only be PSEvar.
        There should be an error otherwise. *)
    fun compare (PSEvar _, PSSet _) = GREATER
      | compare (PSSet _, PSEvar _) = LESS
      | compare (PSSet s1, PSSet s2) = PrioSet.compare (s1, s2)
      | compare (PSEvar (ref (Bound _)), PSEvar (ref (Free _))) = GREATER
      | compare (PSEvar (ref (Free _)), PSEvar (ref (Bound _))) = LESS
      | compare (PSEvar (ref (Free n1)), PSEvar (ref (Free n2))) = compare (w1, w2)
      | compare (PSEvar (ref (Bound w1)), PSEvar (ref (Bound w2))) = Int.compare (n1, n2)

    structure PSEvarMap = SplayMapFn (struct
                                        type ord_key = prioset
                                        val compare = compare
                                      end)

    (* priority set constraint
        PSSub (ps1, ps2): ps1 is a super set of ps2
        PSCons (ps1, ps2): priorities in ps1 is less than or equal to priorities in ps2  *)
    datatype psconstraint =
      PSSup of prioset * prioset
    | PSCons of prioset * prioset 

    (* initialize priority set variables in context *)
    fun psctx_init psevars (psevars: prioset list) = 
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
    fun psconstraints_solver ctx constraints = 
      let 
        fun check_sup_constraint (s1, s2) = PrioSet.equal (PrioSet.different (s1, s2), PrioSet.empty)

        fun solver_fold (constaint, ctx) = 
          case constraint of 
            PSCons _ => ctx
          | PSSup (PSSet _, _) => raise (PSetConstraint "set constant cannot be a superset in the constraint")
          | PSSup (ps as PSEvar _, PSSet s) => 
              (case PSEvarMap.find (ctx, ps) of 
                NONE => raise (PSetConstraints "cannot find psevar in context")   (* this error shouldn't be raised *)
              | SOME s' => 
                  if check_sup_constraint (s', s) then ctx 
                  else PSEvarMap.insert (ctx, ps, PrioSet.union (s', s)))
          | PSSup (ps1 as PSEvar _, ps2 as PSEvar _) =>
              (case (PSEvarMap.find (ctx, ps1), PSEvarMap.find (ctx, ps2)) of 
                (SOME s1, SOME s2) => 
                  if check_sup_constraint (s1, s2) then ctx
                  else PSEvarMap.insert (ctx, ps1, PrioSet.union (s1, s2))
              | _ => raise (PSetConstraint "cannot find psevar in context"))   (* this error shouldn't be raised *)
      in 
        let val ctx' = List.foldl solver_fold ctx constraints
        in
          if PrioSet.collate PrioSet.compare ctx' ctx = EQUAL then ctx'
          else psconstraints_solver ctx' constraints
        end
      end
end
