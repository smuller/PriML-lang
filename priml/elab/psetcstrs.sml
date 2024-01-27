
structure PSetCstrs :> PSETCSTRS = 
struct

    open IL  
    open PSContext
    open ILPrint

    exception PSConstraints of string

    (* priority set constraint
      PSSup (ps1, ps2): ps1 is a super set of ps2
      PSCons (ps1, ps2): priorities in ps1 is less than or equal to priorities in ps2  *)
    datatype psconstraint = 
      PSSup of Context.context * prioset * prioset 
    | PSCons of Context.context * prioset * prioset
    | PSWellformed of Context.context * prioset

    fun psctol (PSSup (_, ps1, ps2)) =
	Layout.mayAlign
	    [Layout.str "sup",
	     Layout.paren(Layout.mayAlign [pstol ps1, Layout.str ",", pstol ps2])]
      | psctol (PSCons (_, ps1, ps2)) =
	Layout.mayAlign
	    [Layout.str "cons",
	     Layout.paren (Layout.mayAlign [pstol ps1, Layout.str ",", pstol ps2])]

    (* PRIORITY SET CONSTRAINTS *)
    (* add superset *)
    fun pscstr_sup ctx ws1 ws2 = [PSSup (ctx, ws1, ws2)]

    (* add constraint *)
    fun pscstr_cons ctx ws1 ws2 = [PSCons (ctx, ws1, ws2)]

    (* add equal *)
    fun pscstr_eq ctx ws1 ws2 = (pscstr_sup ctx ws1 ws2) 
				@ (pscstr_sup ctx ws2 ws1)

    (* add general constraint:
    *   pi = set of initial priorities
    *   pp = set of all possible priorities
    *   pf = set of final priorities
    *   general constraints: pp is superset of pi, pp is superset of pf
    * *)
    (* FIX: pp not superset of pi *)
    fun pscstr_gen ctx pi pp pf = (pscstr_sup ctx pp pi) 
				  @
				  (pscstr_sup ctx pp pf)

    fun pscstr_wf ctx p = [PSWellformed (ctx, p)]

    (* SOLVER FUNCTIONS *)
    (* priority set constraints solver *)

    (* check if s1 is superset of s2 *)
    fun check_sup (s1, s2) = 
      PrioSet.equal (PrioSet.difference (s2, s1), PrioSet.empty)

    (* check if priorities in s1 is less than priorities in s2 *)
    fun check_cons ctx (s1, s2) = 
      PrioSet.foldr 
        (fn (p, b) => 
          (PrioSet.foldr (fn (p', b') => 
            (Context.checkcons ctx p' p) andalso b') true s1) andalso b) 
        true
        s2

    fun solve_pscstrs (psctx: pscontext) (pscstrs: psconstraint list) = 
      let 
        (* retrieve priority of psevar in pscontext. 
         * If psevar is not in pscontext with empty set as the value. *)
        fun getps (psctx, pse) = 
          case PSEvarMap.find (psctx, pse) of 
               SOME s => (psctx, s)
             | NONE => (PSEvarMap.insert (psctx, pse, PrioSet.empty), PrioSet.empty)

        (* solve priority set system from PSSup (s1, s2) constraints, skip PSCons.
         * If s1 is not the superset of s2, add every priorities in s2 to s1. *)
        fun solve (cstr, psctx) = 
          case cstr of 
            PSCons (_, PSSet _, PSSet _) => psctx
          | PSCons (_, PSSet _, ps as PSEvar _) => 
              let val (psctx', _) = getps (psctx, ps) 
              in 
                psctx'
              end
          | PSCons (_, ps as PSEvar _, PSSet _) =>
              let val (psctx', _) = getps (psctx, ps) 
              in 
                psctx'
              end
          | PSCons (_, ps1 as PSEvar _, ps2 as PSEvar _) =>
              let val (psctx', _) = getps (psctx, ps1) 
                  val (psctx'', _) = getps (psctx', ps2)
              in
                psctx''
              end

          | PSSup (_, PSSet _, PSSet _) => psctx
          | PSSup (_, PSSet _, ps as PSEvar _) =>
              let val (psctx', _) = getps (psctx, ps) 
              in 
                psctx'
              end
          | PSSup (_, ps as PSEvar _, PSSet s) => 
              let val (psctx', s') = getps (psctx, ps)
              in
                if check_sup (s', s) then psctx'
                else PSEvarMap.insert (psctx', ps, PrioSet.union(s', s))
              end
          | PSSup (_, ps1 as PSEvar _, ps2 as PSEvar _) =>
              let val (psctx', s1) = getps (psctx, ps1) 
                  val (psctx'', s2) = getps (psctx', ps2)
              in
                if check_sup (s1, s2) then psctx''
                else PSEvarMap.insert (psctx'', ps1, PrioSet.union(s1, s2))
              end
        in 
        let val psctx' = List.foldl solve psctx pscstrs 
        in
          if PSEvarMap.collate PrioSet.compare (psctx', psctx) = EQUAL then psctx'
          else solve_pscstrs psctx' pscstrs
        end
      end


    (* check solutions satifying all psconstraints *)
    fun check_pscstrs_sol (psctx: pscontext) 
                          (pscstrs: psconstraint list) = 
      let 
        fun error_msg (ps1, s1) (ps2, s2) = 
           Layout.tostring (ILPrint.pstol ps1)
           ^ " (" ^ Layout.tostring (ILPrint.pstol (PSSet s1)) ^ ") and "
           ^ Layout.tostring (ILPrint.pstol ps2)
           ^ " (" ^ Layout.tostring (ILPrint.pstol (PSSet s2)) ^ ")"

        (* get set solution in priority set context *)
        fun get_set ps = 
          (case ps of 
             PSSet s => s
           | PSEvar e => 
              (case (PSEvarMap.find (psctx, PSEvar e)) of
                SOME s => s
              | _ => raise (PSConstraints "cannot find psevar in context")))

        (*
          (* check if solved system has empty solution *)
          fun check_empty psctx = 
            if List.all (fn ps => not (PrioSet.isEmpty ps)) (PSEvarMap.listItems psctx) then ()
            else raise (PSConstraints "empty priority set")
        *)

        (* helper function to check set constraint *)
        fun check (PSSup (_, ps1, ps2)) = 
            let val s1 = get_set ps1
                val s2 = get_set ps2
            in
              (if check_sup (s1, s2) then ()
               else raise 
                  (PSConstraints 
                    ("superset violated: " 
                     ^ (error_msg (ps1, s1) (ps2, s2)))))
            end
          | check (PSCons (ctx, ps1, ps2)) =
            let val s1 = get_set ps1
                val s2 = get_set ps2
            in
              (if check_cons ctx (s1, s2) then ()
               else raise 
                  (PSConstraints 
                    ("priority set constraint violated: "
                     ^ (error_msg (ps1, s1) (ps2, s2)))))
            end
      in 
        List.app check pscstrs 
      end
end
