
structure PSetCstrs :> PSETCSTRS = 
struct

    open IL  
    open PSContext

    exception PSConstraints of string

    val all_psconstraints = ref (nil : psconstraint list)

    fun add_psconstraint pscstr = 
      let in 
        all_psconstraints := pscstr :: !all_psconstraints
      end

    fun psconstraint_tostring (PSSup (ps1, ps2)) = 
      "(PSSup (" ^ (Layout.tostring (ILPrint.pstol ps1)) ^ "," ^
      (Layout.tostring (ILPrint.pstol ps2)) ^ "))"

      | psconstraint_tostring (PSCons (ps1, ps2)) = 
      "(PSCons (" ^ (Layout.tostring (ILPrint.pstol ps1)) ^ "," ^
      (Layout.tostring (ILPrint.pstol ps2)) ^ "))"

    fun psconstraints_tostring cs = 
      case cs of 
        []    => "\n"
      | [c]   => psconstraint_tostring c ^ "\n"
      | c::cs => (psconstraint_tostring c) ^ ", " ^ (psconstraints_tostring cs)

    fun print_psconstraints () = 
      print (psconstraints_tostring (!all_psconstraints))

    fun psctx_tostring psctx_list = 
      case psctx_list of
        [] => "\n"
      | [(k, v)] => (Layout.tostring (ILPrint.pstol k)) ^ " : " ^
      (Layout.tostring (ILPrint.pstol (PSSet v))) ^ "\n"
      | (k, v) :: rest => (Layout.tostring (ILPrint.pstol k)) ^ " : " ^
      (Layout.tostring (ILPrint.pstol (PSSet v))) ^ ", " ^ (psctx_tostring rest)

    fun print_psctx psctx = 
      print (psctx_tostring (PSEvarMap.listItemsi psctx))

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
    fun psconstraints_solver (psctx: pscontext) = 
      let 
        fun check_empty_sets psctx = 
          if List.all (fn ps => not (PrioSet.isEmpty ps)) (PSEvarMap.listItems psctx) then ()
          else raise (PSConstraints "empty priority set")

        fun check_sup_constraint (s1, s2) = 
          let val d1 = PrioSet.difference (s1, s2)
              val d2 = PrioSet.difference (s2, s1)
          in
            PrioSet.equal (PrioSet.union (d1, d2), PrioSet.empty)
          end

        fun solver_fold (constraint, psctx) = 
          case constraint of 
            PSCons _ => psctx
          | PSSup (PSSet _, _) => psctx
              (*raise (PSConstraints "set constant cannot be a superset in the constraint")*)
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
              | _ => raise (PSConstraints "cannot find psevar in context"))     (*this error shouldn't be raised *)
      in 
        let val psctx' = List.foldl solver_fold psctx (!all_psconstraints)
        in
          if PSEvarMap.collate PrioSet.compare (psctx', psctx) = EQUAL then 
            (print_psctx psctx'; check_empty_sets psctx'; psctx')
          else psconstraints_solver psctx' 
        end
      end

    (* check (Sync) PSCons constraints in solved system *)
    fun check_psconstraints (ctx: Context.context) (psctx: pscontext) = 
    let 
      (* check if sets satisfy (Sync) PSCons constraints *)
      fun check_sync_cons (s1, s2) = 
        PrioSet.app 
          (fn p => 
            PrioSet.app 
              (fn p' => if Context.checkcons ctx p p' then () else raise (PSConstraints "constraint violated")) 
              s2) 
          s1

      (* helper function to check set constraint *)
      fun check_app (PSSup _) = ()
        | check_app (PSCons (PSSet s1, PSSet s2)) = check_sync_cons (s1, s2)
        | check_app (PSCons (PSSet s, ps as PSEvar _)) = 
            (case PSEvarMap.find (psctx, ps) of
              SOME s' => check_sync_cons (s, s')
            | _ => raise (PSConstraints "cannot find psevar in context"))   (* this error shouldn't be raised *)
        | check_app (PSCons (ps1 as PSEvar _, ps2 as PSEvar _)) = 
            (case (PSEvarMap.find (psctx, ps1), PSEvarMap.find (psctx, ps2)) of 
              (SOME s, SOME s') => check_sync_cons (s, s')
            | _ => raise (PSConstraints "cannot find psevar in context"))   (* this error shouldn't be raised *)
        | check_app (PSCons (ps as PSEvar _, PSSet s')) = 
            (case PSEvarMap.find (psctx, ps) of 
              SOME s => check_sync_cons (s, s')
            | _ => raise (PSConstraints "cannot find psevar in context"))   (* this error shouldn't be raised *)
    in 
      List.app check_app (!all_psconstraints)
    end

end
