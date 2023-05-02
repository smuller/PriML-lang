
structure PSetCstrs :> PSETCSTRS = 
struct

    open IL  
    open PSContext

    structure L = Layout

    exception PSConstraints of string


    (* PRINT FUNCTIONS *)
    val $ = L.str
    val % = L.mayAlign

    fun pscstrsol pscstrs = L.listex "[" "]" ", " (map ILPrint.psctol pscstrs)

    fun psctxkvol (psk, psv) = L.seq [ILPrint.pstol psk, $": ", ILPrint.pstol (PSSet psv)]

    fun psctxol psctx = 
      L.listex "{" "}" "," (map psctxkvol (PSEvarMap.listItemsi psctx))

    fun print_pscstrs pscstrs = L.print (pscstrsol pscstrs, print)

    fun print_psctx psctx = L.print (psctxol psctx, print)


    (* UNIFIED PRIORITY SET CONSTRAINTS *)
    val unified_pscstrs = ref (nil : psconstraint list)

    fun add_unified_pscstrs pscstrs = unified_pscstrs := pscstrs @ (!unified_pscstrs)

    fun clear_unified_pscstrs () = unified_pscstrs := nil

    fun ret_unified_pscstrs () = 
      let val pscstrs = !unified_pscstrs
      in 
        clear_unified_pscstrs ();
        pscstrs
      end


    (* PRIORITY SET CONSTRAINTS *)
    (* add superset *)
    fun pscstr_sup ws1 ws2 = [PSSup (ws1, ws2)]

    (* add constraint *)
    fun pscstr_cons ws1 ws2 = [PSCons (ws1, ws2)]

    (* add equal *)
    fun pscstr_eq ws1 ws2 = (pscstr_sup ws1 ws2) 
                            @ (pscstr_sup ws2 ws1)

    (* add general constraint:
    *   pi = set of initial priorities
    *   pp = set of all possible priorities
    *   pf = set of final priorities
    *   general constraints: pp is superset of pi, pp is superset of pf
    * *)
    fun pscstr_gen pi pp pf = (pscstr_sup pp pi) 
                              @ (pscstr_sup pp pf)


    (* SOLVER FUNCTIONS *)
    (* priority set constraints solver *)
    fun check_sup (s1, s2) = 
      PrioSet.equal (PrioSet.difference (s2, s1), PrioSet.empty)

    fun check_cons ctx (s1, s2) = 
      PrioSet.foldr 
        (fn (p, b) => 
          (PrioSet.foldr (fn (p', b') => 
            (Context.checkcons ctx p' p) andalso b') true s1) andalso b) 
        true
        s2

    fun solve_pscstrs (psctx: pscontext) (pscstrs: psconstraint list) = 
      let 
        fun solve (cstr, psctx) = 
          case cstr of 
            PSCons _ => psctx
          | PSSup (PSSet _, _) => psctx
          | PSSup (ps as PSEvar _, PSSet s) => 
              (case PSEvarMap.find (psctx, ps) of 
                SOME s' => 
                  if check_sup (s', s) then psctx 
                  else PSEvarMap.insert (psctx, ps, PrioSet.union (s', s))
              | _ => PSEvarMap.insert (psctx, ps, s))
          | PSSup (ps1 as PSEvar _, ps2 as PSEvar _) =>
              (case (PSEvarMap.find (psctx, ps1), PSEvarMap.find (psctx, ps2)) of 
                 (SOME s1, SOME s2) => 
                   if check_sup (s1, s2) then psctx
                   else PSEvarMap.insert (psctx, ps1, PrioSet.union (s1, s2))
               | (SOME s1, NONE) => PSEvarMap.insert (psctx, ps2, PrioSet.empty)
               | (NONE, SOME s2) => PSEvarMap.insert (psctx, ps1, s2)
               | (NONE, NONE) => 
                   let val psctx' = PSEvarMap.insert (psctx, ps1, PrioSet.empty)
                   in
                     PSEvarMap.insert (psctx, ps2, PrioSet.empty)
                   end)
        in 
        let val psctx' = List.foldl solve psctx pscstrs 
        in
          if PSEvarMap.collate PrioSet.compare (psctx', psctx) = EQUAL then psctx'
          else solve_pscstrs psctx' pscstrs
        end
      end


    (* check solutions *)
    fun check_pscstrs_sol (ctx: Context.context) 
                          (psctx: pscontext) 
                          (pscstrs: psconstraint list) = 
      let 
        fun error_msg (ps1, s1) (ps2, s2) = 
           L.tostring (ILPrint.pstol ps1)
           ^ " (" ^ L.tostring (ILPrint.pstol (PSSet s1)) ^ ") and "
           ^ L.tostring (ILPrint.pstol ps2)
           ^ " (" ^ L.tostring (ILPrint.pstol (PSSet s2)) ^ ")"

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
        fun check (PSSup (ps1, ps2)) = 
            let val s1 = get_set ps1
                val s2 = get_set ps2
            in
              (if check_sup (s1, s2) then ()
               else raise 
                  (PSConstraints 
                    ("superset violated: " 
                     ^ (error_msg (ps1, s1) (ps2, s2)))))
            end
          | check (PSCons (ps1, ps2)) =
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
