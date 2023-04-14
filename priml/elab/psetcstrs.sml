
structure PSetCstrs :> PSETCSTRS = 
struct

    open IL  
    open PSContext

    structure L = Layout

    exception PSConstraints of string

    val $ = L.str
    val % = L.mayAlign

    val all_psconstraints = ref (nil : psconstraint list)

    (* clear priority set constraints *)
    fun clear_psconstraints () = all_psconstraints := nil

    (* add new priority set constraint *)
    fun add_psconstraint pscstr = 
      all_psconstraints := pscstr :: (!all_psconstraints)

    (* add superset *)
    fun pscstr_sup ws1 ws2 = add_psconstraint (PSSup (ws1, ws2))

    (* add constraint *)
    fun pscstr_cons ws1 ws2 = add_psconstraint (PSCons (ws1, ws2))

    (* add equal *)
    fun pscstr_eq ws1 ws2 = (pscstr_sup ws1 ws2;
                             pscstr_sup ws2 ws1)

    (* add general constraint:
    *   pi = set of initial priorities
    *   pp = set of all possible priorities
    *   pf = set of final priorities
    *   general constraints: pp is superset of pi, pp is superset of pf
    * *)
    fun pscstr_gen pi pp pf = (pscstr_sup pp pi; 
                               pscstr_sup pp pf)


    (* PRINT FUNCTIONS *)
    fun pscstrol (PSSup (ps1, ps2))  = 
          %[$"sup", L.paren (L.seq [ILPrint.pstol ps1, $", ", ILPrint.pstol ps2])]
      | pscstrol (PSCons (ps1, ps2)) = 
          %[$"cons", L.paren (L.seq [ILPrint.pstol ps1, $", ", ILPrint.pstol ps2])]

    fun pscstrsol pscstrs = L.listex "[" "]" ", " (map pscstrol pscstrs)

    fun psctxkvol (psk, psv) = L.seq [ILPrint.pstol psk, $": ", ILPrint.pstol (PSSet psv)]

    fun psctxol psctx = 
      L.listex "{" "}" "," (map psctxkvol (PSEvarMap.listItemsi psctx))

    fun print_pscstrs () = L.print (pscstrsol (!all_psconstraints), print)

    fun print_psctx psctx = L.print (psctxol psctx, print)


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

    fun solve_pscstrs (psctx: pscontext) = 
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
              | _ => 
                  (* this error shouldn't be raised *)
                  raise (PSConstraints "cannot find psevar in context"))
          | PSSup (ps1 as PSEvar _, ps2 as PSEvar _) =>
              (case (PSEvarMap.find (psctx, ps1), PSEvarMap.find (psctx, ps2)) of 
                (SOME s1, SOME s2) => 
                  if check_sup (s1, s2) then psctx
                  else PSEvarMap.insert (psctx, ps1, PrioSet.union (s1, s2))
              | _ => 
                  (*this error shouldn't be raised *)
                  raise (PSConstraints "cannot find psevar in context"))     
      in 
        let val psctx' = List.foldl solve psctx (!all_psconstraints)
        in
          if PSEvarMap.collate PrioSet.compare (psctx', psctx) = EQUAL then 
            (print_psctx psctx'; print "\n";
             psctx')
          else solve_pscstrs psctx' 
        end
      end

    (* check solutions *)
    fun check_pscstrs_sol (ctx: Context.context) (psctx: pscontext) = 
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
      List.app check (!all_psconstraints)
    end
end
