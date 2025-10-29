
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

    val next_rvar = ref 0

    fun new_rvar () =
	RVar (!next_rvar)
	before (verbprint ("new rvar: " ^ (Int.toString (!next_rvar)) ^ "\n");
		next_rvar := (!next_rvar) + 1)

    fun new_prioset () =
	([], new_rvar ())

    (* SOLVER FUNCTIONS *)
    (* priority set constraints solver *)

    (* An assignment A is a map from refinement vars to concrete refinements *)
    type assign = (V.var * pconstraint list) IntMap.map

    fun string_of_assign assign =
	IntMap.foldli
	(fn (n, (v, cs), s) =>
	    s ^ "\n"
	    ^ "'ws" ^ (Int.toString n) ^ " : "
	    ^ (Layout.tostring (ILPrint.pstol ([], RConcrete (v, cs))))
	)
	""
	assign

    (* We can substitute assignments into various things *)

    fun assign_in_rfmt assign rfmt =
	case rfmt of
	    RConcrete x => x
	  | RVar n =>
	    (case IntMap.find (assign, n) of
		 SOME x => x
	       | NONE => raise (Context.Absent ("refinement var", "'ws" ^ (Int.toString n))))

    fun singleton (k, v) =
	VM.insert (VM.empty, k, v)

    fun prsubcs s pcs =
	List.map
	    (fn (p1, p2) => (Subst.prsubsp s p1, Subst.prsubsp s p2))
	    pcs

    (* Turn x = [v | constrs] into [x/v]constrs *)
    fun close_rfmt assign p (xv, pcs, evs) =
	let val s' = singleton (xv, p)
	in
	    prsubcs s' pcs
	end

	(* This returns (and takes) an extra set of existentially quantified
	 * variables resulting from substituting constraint sets *)
    fun do_pendsubs assign (ps: arg_subst subst) (rfmt_var, rfmt_cs, exist_vars) =
	VM.foldli
	    (fn (v, SubstVar v', (rfmt_var, rfmt_cs, exist_vars)) =>
		(rfmt_var, prsubcs (singleton (v, PVar v')) rfmt_cs,
		 List.filter (fn v'' => not (V.eq (v'', v))) exist_vars)
	    | (v, SubstPrio prio, (rfmt_var, rfmt_cs, exist_vars)) =>
	      (rfmt_var, prsubcs (singleton (v, prio)) rfmt_cs,
	      List.filter (fn v'' => not (V.eq (v'', v))) exist_vars)
	    | (v, SubstSet pset, (rfmt_var, rfmt_cs, exist_vars)) =>
	      (rfmt_var, (close_rfmt assign (PVar v) (assign_in_prioset assign pset)) @ rfmt_cs,
	      v::(List.filter (fn v'' => not (V.eq (v'', v))) exist_vars))
	    | (v, DontSubst, rfmt) => rfmt
	    )
	    (rfmt_var, rfmt_cs, exist_vars)
	    ps
				  
    (* Get a refinement for a prioset under assign by performing the assignments
     * and then the pending substitutions.*)
    and assign_in_prioset assign (substs, rfmt) =
	let val (v, ps) = assign_in_rfmt assign rfmt
	    fun do_allsubs subs (v, ps, evs) =
		case subs of
		    [] => (v, ps, evs)
		  | s::subs => do_pendsubs assign s (do_allsubs subs (v, ps, evs))
	in
	    do_allsubs substs (v, ps, [])
	end

    fun string_of_pconstraint assign psc =
	(case psc of
	     PSCons (ctx, p1, p2) =>
	     ("(" ^ Layout.tostring (Context.ctol ctx) ^ ") |- ("
	      ^ (Layout.tostring (ILPrint.pstol p1)) ^ ") <= ("
	      ^ (Layout.tostring (ILPrint.pstol p2)) ^ ")")
	   | PSSup (ctx, p1, p2) =>
	     ("(" ^ Layout.tostring (Context.ctol ctx) ^ ") |- ("
	      ^ (Layout.tostring (ILPrint.pstol p2)) ^ ") ==> ("
	      ^ (Layout.tostring (ILPrint.pstol p1)) ^ ")")
	   | PSWellformed (ctx, p) =>
	     ("(" ^ Layout.tostring (Context.ctol ctx) ^ ") |- ("
	      ^ (Layout.tostring (ILPrint.pstol p)) ^ ")")
	)
	^
	(case assign of
	     NONE => ""
	   | SOME assign =>
	     (case psc of
		  PSCons (ctx, p1, p2) =>
		  let val (rv1, rcs1, _) = assign_in_prioset assign p1
		      val (rv2, rcs2, _) = assign_in_prioset assign p2
		      val ps1 = ([], RConcrete (rv1, rcs1))
		      val ps2 = ([], RConcrete (rv2, rcs2))
		  in
		      "(" ^ Layout.tostring (Context.ctol ctx) ^ ") |- ("
		      ^ (Layout.tostring (ILPrint.pstol ps1)) ^ ") <= ("
		      ^ (Layout.tostring (ILPrint.pstol ps2)) ^ ")"
		  end
		| PSSup (ctx, p1, p2) =>
		  let val (rv1, rcs1, _) = assign_in_prioset assign p1
		      val (rv2, rcs2, _) = assign_in_prioset assign p2
		      val ps1 = ([], RConcrete (rv1, rcs1))
		      val ps2 = ([], RConcrete (rv2, rcs2))
		  in
		      "(" ^ Layout.tostring (Context.ctol ctx) ^ ") |- ("
		      ^ (Layout.tostring (ILPrint.pstol ps2)) ^ ") ==> ("
		      ^ (Layout.tostring (ILPrint.pstol ps1)) ^ ")"
		  end
		| PSWellformed (ctx, p) =>
		  let val (rv, rcs, _) = assign_in_prioset assign p
		      val ps = ([], RConcrete (rv, rcs))
		  in
		      "(" ^ Layout.tostring (Context.ctol ctx) ^ ") |- ("
		      ^ (Layout.tostring (ILPrint.pstol ps)) ^ ")"
		  end
	     )
	)
	    

    (* The context has bindings like p : [v | constraints].
     * Return these as a list [p/v]constraints *)
    fun constraints_in_ctx assign ctx =
	List.foldl
	    (fn (v, cs) =>
		case Context.var ctx (Variable.basename v) of
		(Poly ({tys}, TPrio p), v, _) =>
		    (close_rfmt assign (PVar v) (assign_in_prioset assign p)) @ cs
	      | _ => cs
	    )
	    []
	    (Context.prio_vars ctx)

	    
    (* check if priorities in s1 are less than priorities in s2 *)
    fun check_cons assign ctx (s1, s2) =
	let val (v1, v2) = (V.namedvar "prio__s1", V.namedvar "prio__s2")
	    val (rv1, rcs1, evs1) = assign_in_prioset assign s1
	    val c1 = close_rfmt assign (IL.PVar v1) (rv1, rcs1, evs1)
	    val (rv2, rcs2, evs2) = assign_in_prioset assign s2
	    val c2 = close_rfmt assign (IL.PVar v2) (rv2, rcs2, evs2)
	    val z3 =
		Z3.setup
		    (SOME (string_of_pconstraint (SOME assign) (PSCons (ctx, s1, s2))))
		    ctx
		    ([v1, v2] @ evs1 @ evs2)
	    val z3 =
		List.foldl
		    (fn (c, z3) => Z3.compose (z3, Z3.of_constraint c))
		    z3
		    (constraints_in_ctx assign ctx)
	    val z3 =
		List.foldl
		    (fn (c, z3) => Z3.compose (z3, Z3.of_constraint c))
		    z3
		    (c1 @ c2)
	    val z3 =
		(* Add the constraint s2 < s1... *)
		Z3.compose (z3, Z3.negate_constraint (IL.PVar v1, IL.PVar v2))
	in
	    verbprint z3;
	    (*... and check that the system is UNsatisfiable *)
	    not (Z3.check z3)
	end

    (* check if s1 implies s2, that is, if the set of possible priorities under
     * s1 is a subset of the set of possible priorities under s2 *)
    fun check_sub assign ctx (s1, s2) =
	let val v = Variable.namedvar "prio__s"
	    val (rv1, rcs1, evs1) = assign_in_prioset assign s1
	    val c1 = close_rfmt assign (IL.PVar v) (rv1, rcs1, evs1)
	    val (rv2, rcs2, evs2) = assign_in_prioset assign s2
	    val c2 = close_rfmt assign (IL.PVar v) (rv2, rcs2, evs2)
	    (* We want to assert ~(/\c1 => /\c2), which is the same as /\c1 /\ ~(/\c2) *)
	in
	    if List.length c2 = 0 then
		(* s2 is T, so the implication is trivially satisfied *)
		true
	    else
		let val z3 =
			Z3.setup
			    (SOME (string_of_pconstraint (SOME assign) (PSSup (ctx, s2, s1))))
			    ctx
			    ([v] @ evs1 @ evs2)
		    val z3 =
			List.foldl
			    (fn (c, z3) => Z3.compose (z3, Z3.of_constraint c))
			    z3
			    (constraints_in_ctx assign ctx)
		    val z3 = Z3.compose (z3, Z3.comment "End ctx constraints\n")
		    val z3 =
			List.foldl
			    (fn (c, z3) => Z3.compose (z3, Z3.of_constraint c))
			    z3
			    c1
		    val z3 =
			(* Add the constraint ~(/\ c2)... *)
			Z3.compose (z3, Z3.negate_and_constraints c2)
		in
		    verbprint (z3);
		    (*... and check that the system is UNsatisfiable *)
		    not (Z3.check z3)
		end
	end

    fun priowf ctx dv (IL.PVar v) =
	V.eq (dv, v)
	orelse
	((let val _ = Context.var_fail ctx (Variable.show v)
	  in true
	  end)
	 handle _ => false)
      | priowf ctx dv (IL.PConst s) =
	((let val _ = Context.var_fail ctx s
	  in true
	  end)
	 handle _ => false)
	    
    (* Check if ps is well-formed, i.e., has no unbound priority vars *)
    fun check_wf assign ctx ps =
	let val (rv, rcs, _) = assign_in_prioset assign ps
	    val _ = verbprint "checking "
	    val _ = verbprint (string_of_pconstraint (SOME assign) (PSWellformed (ctx, ps)))
	in
	    List.foldl
		(fn ((p1, p2), wf) =>
		    wf andalso
		    (priowf ctx rv p1) andalso (priowf ctx rv p2))
		true
		rcs
	end

    fun check assign constraint =
	let val _ = verbprint "checking "
	    val _ = verbprint (string_of_pconstraint (SOME assign) constraint)
		    
	    val sat = case constraint of
			  PSSup (ctx, p1, p2) => check_sub assign ctx (p2, p1)
			| PSCons (ctx, p1, p2) => check_cons assign ctx (p1, p2)
			| PSWellformed (ctx, p) => check_wf assign ctx p
	in
	    sat
	    before (if sat then verbprint "SAT\n" else verbprint "UNSAT\n")
	end

    exception Unsolvable of psconstraint

    (* Weaken a constraint of the form "s1 ==> s2 *)
    fun weaken_sub assign ctx (s1, (substs2, rfmt2)) =
	case rfmt2 of
	    RConcrete _ => NONE
	  | RVar n =>
	    let val (rv2, rcs2) =
		    case IntMap.find (assign, n) of
			SOME x => x
		      | NONE => raise (Context.Absent ("refinement var", "'ws" ^ (Int.toString n)))
		fun check_one c =
		    (* Build back dummy refinements to reuse the
		     * constraint checking code to check just
		     * (A(\Gamma) /\ A(s1) ==> A(c) *)
		    check_sub assign ctx
			      (s1,
			       (substs2, RConcrete (rv2, [c])))
		val new_rcs2 = List.filter check_one rcs2
	    in
		(* Assertion: the number of qualifiers should have decreased *)
		if List.length new_rcs2 >= List.length rcs2 then
		    (print "Uh oh: didn't eliminate qualifiers?";
		     raise (Unsolvable (PSSup (ctx, (substs2, rfmt2), s1))))
		else
		    SOME (n, IntMap.insert (assign, n, (rv2, new_rcs2)))
	    end

    fun weaken_wf assign ctx (substs, rfmt) =
	case rfmt of
	    RConcrete _ => NONE
	  | RVar n => 
	    let val (rv, rcs) =
		    case IntMap.find (assign, n) of
			SOME x => x
		      | NONE => raise (Context.Absent ("refinement var", "'ws" ^ (Int.toString n)))
		fun check_one c =
		    check_wf assign ctx (substs, RConcrete (rv, [c]))
		val new_rcs =
		    List.filter check_one rcs
	    in
		SOME (IntMap.insert (assign, n, (rv, new_rcs)))
	    end


end
