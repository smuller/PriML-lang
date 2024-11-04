
structure PSetCstrs :> PSETCSTRS = 
struct

    open IL  
    (* open PSContext *)
    open ILPrint
	     
    structure IM = IntMap

    type pscontext = Context.pscontext

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
      | psctol (PSWellformed (_, ps)) =
	Layout.mayAlign
	    [Layout.str "wf",
	     Layout.paren (pstol ps)]

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
	PrioSet.isSubset (s2, s1)
(*      PrioSet.equal (PrioSet.difference (s2, s1), PrioSet.empty) *)

    (* check if priorities in s1 is less than priorities in s2 *)
    fun check_cons psctx ctx (s1, s2) = 
      PrioSet.foldr 
        (fn (p, b) => 
          (PrioSet.foldr (fn (p', b') => 
            (Context.checkcons psctx ctx p' p) andalso b') true s1) andalso b) 
        true
        s2

    

    fun baseps ps =
	case ps of
	    PSEvar (ref (Bound ps)) => baseps ps
	  | PSSet set => PSSet set
	  | _ => ps

    fun inst_prio ctx get_set p =
	case p of
	    PEvar (ref (Bound p)) => inst_prio ctx get_set p
	  | PEvar _ => PrioSet.singleton p
	  | PVar v =>
	    (
	     case Context.rem ctx (V.basename v) of
		 SOME (ctx, (Poly (_, TPrio ps), _, _)) =>
		 inst_set ctx get_set (get_set ps)
	       | _ => PrioSet.singleton p
	    )
	  | PConst s =>
	    (case Context.rem ctx s of
		 SOME (ctx, (Poly (_, TPrio ps), _, _)) =>
		 inst_set ctx get_set (get_set ps)
	       | _ => PrioSet.singleton p
	    )

    and inst_set ctx get_set set =
	PrioSet.foldl
	    (fn (p, set) => PrioSet.union (set, inst_prio ctx get_set p))
	    PrioSet.empty
	    set
	(*
	let val ps = new_psevar ()
	in
	    (ps,
	     List.fold_left
		 (fn (p, cs) =>
		     let val (ps', cs') = inst_prio ctx p
		     in
			 (PSSup (Context.empty, ps, ps'))::(cs' @ cs)
		     end
		 )
		 []
		 set
	    )
	end*)
	    (*
	    *)

	    (*
    fun inst_ps ctx (PSEvar (ref (Bound ps))) = inst_ps ctx ps
      | inst_ps ctx (PSSet set) = inst_set ctx set
      | inst_ps ctx ps = ps
	    *)

    

		      (*
    fun dosub ps =
	sub_in_ps VM.empty ps

    fun dosub_cstr cstr =
	case cstr of
	    PSCons (ctx, ps1, ps2) => (* PSCons (ctx, dosub ps1, dosub ps2) *)
	    PSCons (ctx,
		    inst_ps ctx (dosub ps1),
		    inst_ps ctx (dosub ps2))
	  | PSSup (ctx, ps1, ps2) =>
	    PSSup (Context.empty,
		   inst_ps ctx (dosub ps1),
		   inst_ps ctx (dosub ps2))
	  | PSWellformed (ctx, ps) => PSWellformed (ctx, dosub ps)
		      *)

    fun error_msg ctx (ps1, s1) (ps2, s2) =
	(case ctx of
	     SOME ctx => " (" ^ Layout.tostring (Context.ctol ctx)
			 ^ ") =>"
	   | NONE => ""
	)
        ^ Layout.tostring (ILPrint.pstol ps1)
        ^ " (" ^ Layout.tostring (ILPrint.pstol (PSSet s1)) ^ ") and "
        ^ Layout.tostring (ILPrint.pstol ps2)
        ^ " (" ^ Layout.tostring (ILPrint.pstol (PSSet s2)) ^ ")"

    fun error_msg_set ctx (ps1, s1) s2 =
	(case ctx of
	     SOME ctx => " (" ^ Layout.tostring (Context.ctol ctx)
			 ^ ") =>"
	   | NONE => ""
	)
        ^ Layout.tostring (ILPrint.pstol ps1)
	^ "(" ^ Layout.tostring (ILPrint.pstol (PSSet s1)) ^ ") and "
        ^ Layout.tostring (ILPrint.pstol (PSSet s2))

    fun error_msg1 ctx (ps1, s1) =
	(case ctx of
	     SOME ctx => " (" ^ Layout.tostring (Context.ctol ctx)
			 ^ ") =>"
	   | NONE => ""
	)
        ^ Layout.tostring (ILPrint.pstol ps1)
        ^ " (" ^ Layout.tostring (ILPrint.pstol (PSSet s1)) ^ ")"
		      
    fun solve_pscstrs (psctx: pscontext) (pscstrs: psconstraint list) = 
      let 
        (* retrieve priority of psevar in pscontext. 
         * If psevar is not in pscontext with empty set as the value. *)
	  fun get_set ps = 
              case ps of 
		  PSSet s => s
		| PSPendSub (es, ps) =>
		  Context.sub_in_set es (get_set ps)
		| PSEvar (ref (Bound ps)) => get_set ps
		| PSEvar (ref (Free i)) => 
		  (case (IM.find (psctx, i)) of
                       SOME s => s
		    |  NONE => PrioSet.empty
		  )
	  fun make_sup (psctx, ps1, s2) =
	      case ps1 of
	          PSEvar (ref (Free i)) =>
		  IM.insert (psctx, i, s2)
			    (*
		| PSEvar r =>
		  let val ref (Free i) = new_ebind () in
		      r := Free i;
		      IM.insert (psctx, i, s2)
		  end
			    *)
		| PSPendSub (s, ps) => make_sup (psctx, ps, s2)
		| PSSet s1 =>
		  raise 
		      (PSConstraints 
			   ("superset violated: " 
			    ^ (error_msg_set NONE (ps1, s1) s2)))
		| PSEvar (ref (Bound ps)) =>
		  raise 
		      (PSConstraints 
			   ("superset violated: " 
			    ^ (error_msg_set NONE (ps1, get_set ps) s2)))

          (* solve priority set system from PSSup (s1, s2) constraints, 
	   * skip PSCons and SWellFormed (for now).
           * If s1 is not the superset of s2, add every priorities in s2 to s1.
	   *)
          fun solve (cstr, psctx) =
          case cstr of 
            PSCons _ => psctx

          | PSSup (ctx, ps1, ps2) =>
	    let (*val s1 = inst_set ctx get_set (get_set ps1)
                val s2 = inst_set ctx get_set (get_set ps2) *)
		val s1 = get_set ps1
		val s2 = get_set ps2
		val _ = verb (fn () => print (error_msg NONE (ps1, s1) (ps2, s2)))
		val _ = verbprint "\n"
	    in
		if check_sup (s1, s2) then psctx
		else make_sup (psctx, ps1, PrioSet.union(s1, s2))
	    end

	  | PSWellformed _ => psctx (* XXX *)
        in 
        let val psctx' = List.foldl solve psctx pscstrs 
        in
          if IM.collate PrioSet.compare (psctx', psctx) = EQUAL then psctx'
          else solve_pscstrs psctx' pscstrs
        end
	  end


    (* check solutions satifying all psconstraints *)
    fun check_pscstrs_sol (psctx: pscontext) 
                          (pscstrs: psconstraint list) = 
      let 
          

          (* get set solution in priority set context *)
	  fun get_set ps = 
              case ps of 
		  PSSet s => s
		| PSPendSub (es, ps) =>
		  Context.sub_in_set es (get_set ps)
		| PSEvar (ref (Bound ps)) => get_set ps
		| PSEvar (ref (Free i)) => 
		  (case (IM.find (psctx, i)) of
                       SOME s => s
		    |  NONE => PrioSet.empty
		  )

        (*
          (* check if solved system has empty solution *)
          fun check_empty psctx = 
            if List.all (fn ps => not (PrioSet.isEmpty ps)) (PSEvarMap.listItems psctx) then ()
            else raise (PSConstraints "empty priority set")
        *)

        (* helper function to check set constraint *)
        fun check (PSSup (ctx, ps1, ps2)) = 
            let val s1 = inst_set ctx get_set (get_set ps1)
                val s2 = inst_set ctx get_set (get_set ps2)
            in
              (if check_sup (s1, s2) then ()
               else raise 
                  (PSConstraints 
                    ("superset violated: " 
                     ^ (error_msg NONE (ps1, s1) (ps2, s2)))))
            end
          | check (PSCons (ctx, ps1, ps2)) =
            let val s1 = get_set ps1
                val s2 = get_set ps2
            in
              (if check_cons psctx ctx (s1, s2) then ()
               else raise 
                  (PSConstraints 
                    ("priority set constraint violated: "
                     ^ (error_msg (SOME ctx) (ps1, s1) (ps2, s2)))))
            end
	  | check (PSWellformed (ctx, ps)) =
	    let val s = inst_set ctx get_set (get_set ps)
	    in
		if PrioSet.exists
		       (fn PEvar _ =>
			   raise (PSConstraints "shouldn't happen")
		       | PVar v =>
			 ((Context.var_fail ctx (V.basename v); false)
			  handle Context.Absent _ => true)
		       | PConst s => 
			 ((Context.var_fail ctx s; false)
			  handle Context.Absent _ => true)
		       )
		       s
		then
		    raise
			(PSConstraints
			     ("well-formedness constraint violated: "
			      ^ (error_msg1 (SOME ctx) (ps, s))))
		else ()
	    end
      in 
        List.app check pscstrs 
      end
end
