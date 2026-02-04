
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
    datatype psconstraint_type = 
      PSSup of Context.context * prioset * prioset 
    | PSCons of Context.context * prioset * prioset
    | PSWellformed of Context.context * prioset

    type psconstraint =
	 {typ : psconstraint_type,
	  loc : Pos.pos,
	  msg : string}

    fun type_of ({typ, ...}: psconstraint) = typ
    fun loc_of ({loc, ...}: psconstraint) = loc
    fun msg_of ({msg, ...}: psconstraint) = msg
	     
    fun psctol pc =
	let
	    val $ = Layout.str
	    val % = Layout.mayAlign
	in
	    % [$(Pos.toString (loc_of pc)),
	       $("(" ^ (msg_of pc) ^ ")"),
	       (case type_of pc of
		    PSCons (_, p1, p2) =>
		    %[$"|- (", ILPrint.pstol p1,
		      $") <= (", ILPrint.pstol p2, $")"]
		  | PSSup (_, p1, p2) =>
		    %[$"|- (", ILPrint.pstol p2,
		      $") ==> (", ILPrint.pstol p1, $")"]
		  | PSWellformed (_, p) =>
		    %[$"|- (", ILPrint.pstol p, $")"]
	       )
	      ]
	end

    fun depends_on_rvar changed const =
	case type_of const of
	    PSSup (ctx, _, (_, (RVar n))) =>
	    n = changed
	    orelse Context.has_rfmtvar ctx changed
	  | (PSSup (ctx, _, _)) =>
	    Context.has_rfmtvar ctx changed
	  | _ => false
	    
    (* PRIORITY SET CONSTRAINTS *)
    (* add superset *)
    fun pscstr_sup ctx ws1 ws2 loc msg =
	[{typ=PSSup (ctx, ws1, ws2), loc=loc, msg=msg}]

    (* add constraint *)
    fun pscstr_cons ctx ws1 ws2 loc msg =
	[{typ=PSCons (ctx, ws1, ws2), loc=loc, msg=msg}]

    (* add equal *)
    fun pscstr_eq ctx ws1 ws2 loc msg = (pscstr_sup ctx ws1 ws2 loc msg) 
				@ (pscstr_sup ctx ws2 ws1 loc msg)

    (* add general constraint:
    *   pi = set of initial priorities
    *   pp = set of all possible priorities
    *   pf = set of final priorities
    *   general constraints: pp is superset of pi, pp is superset of pf
    * *)
    (* FIX: pp not superset of pi *)
    fun pscstr_gen ctx pi pp pf loc msg = (pscstr_sup ctx pp pi loc msg) 
				  @
				  (pscstr_sup ctx pp pf loc msg)

    fun pscstr_wf ctx p loc msg =
	[{typ=PSWellformed (ctx, p), loc=loc, msg=msg}]

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
    fun close_rfmt assign p (xv, pcs) =
	let val s' = singleton (xv, p)
	in
	    prsubcs s' pcs
	end

	(* This returns (and takes) an extra set of existentially quantified
	 * variables and constraints on them resulting from substituting
	 * constraint sets *)
    fun do_pendsubs assign (ps: arg_subst subst)
		    (rfmt_var, rfmt_cs, exist_vars, exist_cons) =
	VM.foldli
	    (fn (v, SubstVar v', (rfmt_var, rfmt_cs, exist_vars, exist_cons)) =>
		(rfmt_var, prsubcs (singleton (v, PVar v')) rfmt_cs,
		 exist_vars, (* Invariant: exist_vars should be fresh, so
			      * no need to check if v is in it *)
		 exist_cons)
	    | (v, SubstPrio prio, (rfmt_var, rfmt_cs, exist_vars, exist_cons)) =>
	      (rfmt_var, prsubcs (singleton (v, prio)) rfmt_cs,
	       exist_vars, exist_cons)
	    | (v, SubstSet pset, (rfmt_var, rfmt_cs, exist_vars, exist_cons)) =>
	      (case IL.is_singleton pset of
		   SOME prio =>
		   (* Special case where this is secretly a SubstPrio *)
		   (rfmt_var, prsubcs (singleton (v, prio)) rfmt_cs,
		    exist_vars, exist_cons)
		 | NONE => 
	      let val (ps_v, ps_cons, ps_evars, ps_econs) =
		      assign_in_prioset assign pset
		  (* Alpha rename v to maintain the invariant that
		   * exist_vars are all fresh*)
		  val fresh_v = Variable.namedvar (Variable.basename v)
		  val v_subs = singleton (v, PVar fresh_v)
	      in
		  (rfmt_var,
		   prsubcs v_subs rfmt_cs,
		   fresh_v::exist_vars,
		   (close_rfmt assign (PVar fresh_v) (ps_v, ps_cons))
		   @ (prsubcs v_subs exist_cons))
	      end
	      )
	    | (v, DontSubst, rfmt) => rfmt
	    )
	    (rfmt_var, rfmt_cs, exist_vars, exist_cons)
	    ps
				  
    (* Get a refinement for a prioset under assign by performing the assignments
     * and then the pending substitutions.*)
    and assign_in_prioset assign (substs, rfmt) =
	let val (v, ps) = assign_in_rfmt assign rfmt
	    fun do_allsubs subs (v, ps, evs, ecs) =
		let val _ = verb (fn () => (print (Layout.tostring (ILPrint.pstol (subs, RConcrete (v, ps @ ecs))));
					    print "\n\n"))
		    val (v', ps', evs', ecs') =
			case subs of
			    [] => (v, ps, evs, ecs)
			  | s::subs => do_pendsubs assign s (do_allsubs subs (v, ps, evs, ecs))
		in
		    verb
			(fn () =>
			     (print (Layout.tostring (ILPrint.pstol ([], RConcrete (v', ps' @ ecs'))));
			      print "\n\n"));
		    (v', ps', evs', ecs')
		end
	in
	    do_allsubs substs (v, ps, [], [])
	end

    fun string_of_pconstraint_type assign psc =
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
	     (* XXX should actually also print out the existential
	      * constraints, but that'll require a special pretty-printer *)
	     (case psc of
		  PSCons (ctx, p1, p2) =>
		  let val (rv1, rcs1, _,  _) = assign_in_prioset assign p1
		      val (rv2, rcs2, _,  _) = assign_in_prioset assign p2
		      val ps1 = ([], RConcrete (rv1, rcs1))
		      val ps2 = ([], RConcrete (rv2, rcs2))
		  in
		      "(" ^ Layout.tostring (Context.ctol ctx) ^ ") |- ("
		      ^ (Layout.tostring (ILPrint.pstol ps1)) ^ ") <= ("
		      ^ (Layout.tostring (ILPrint.pstol ps2)) ^ ")"
		  end
		| PSSup (ctx, p1, p2) =>
		  let val (rv1, rcs1, _,  _) = assign_in_prioset assign p1
		      val (rv2, rcs2, _,  _) = assign_in_prioset assign p2
		      val ps1 = ([], RConcrete (rv1, rcs1))
		      val ps2 = ([], RConcrete (rv2, rcs2))
		  in
		      "(" ^ Layout.tostring (Context.ctol ctx) ^ ") |- ("
		      ^ (Layout.tostring (ILPrint.pstol ps2)) ^ ") ==> ("
		      ^ (Layout.tostring (ILPrint.pstol ps1)) ^ ")"
		  end
		| PSWellformed (ctx, p) =>
		  let val (rv, rcs, _,  _) = assign_in_prioset assign p
		      val ps = ([], RConcrete (rv, rcs))
		  in
		      "(" ^ Layout.tostring (Context.ctol ctx) ^ ") |- ("
		      ^ (Layout.tostring (ILPrint.pstol ps)) ^ ")"
		  end
	     )
	)

    fun string_of_pconstraint assign psc =
	string_of_pconstraint_type assign (type_of psc)

    (* The context has bindings like p : [v | constraints].
     * Return these as a pair
     * (existential vars,  list [p/v]constraints @ existential constraints) *)
    fun constraints_in_ctx assign ctx =
	List.foldl
	    (fn (v, (evs, cs)) =>
		case Context.var ctx (Variable.basename v) of
		    (Poly ({tys}, TPrio p), v, _) =>
		    let val (p_v, p_cons, p_evs, p_ecs) =
			    assign_in_prioset assign p
		    in
			(p_evs @ evs,
			 (close_rfmt assign (PVar v) (p_v, p_cons))
			 @ p_ecs @ cs)
		    end
		  | _ => (evs, cs)
	    )
	    ([], [])
	    (Context.prio_vars ctx)

	    
    (* check if priorities in s1 are less than priorities in s2 *)
    fun check_cons assign ctx (s1, s2) =
	let val (v1, v2) = (V.namedvar "prio__s1", V.namedvar "prio__s2")
	    val (rv1, rcs1, evs1, ecs1) = assign_in_prioset assign s1
	    val c1 = close_rfmt assign (IL.PVar v1) (rv1, rcs1)
	    val (rv2, rcs2, evs2, ecs2) = assign_in_prioset assign s2
	    val c2 = close_rfmt assign (IL.PVar v2) (rv2, rcs2)
	    val (ctx_evs, ctx_cs) = constraints_in_ctx assign ctx
	    val z3 =
		Z3.setup
		    (SOME (string_of_pconstraint_type (SOME assign) (PSCons (ctx, s1, s2))))
		    ctx
		    ([v1, v2] @ evs1 @ evs2 @ ctx_evs)
	    val z3 =
		List.foldl
		    (fn (c, z3) => Z3.add_constraint (z3, c))
		    z3
		    (ctx_cs @ ecs1 @ ecs2)
	    val z3 =
		List.foldl
		    (fn (c, z3) => Z3.add_constraint (z3, c))
		    z3
		    (c1 @ c2)
	    val z3 =
		(* Add the constraint s2 < s1... *)
		Z3.add_negated_constraint (z3, (IL.PVar v1, IL.PVar v2))
	in
	    (* verbprint z3; *)
	    (*... and check that the system is UNsatisfiable *)
	    not (Z3.check z3)
	end

    (* check if s1 implies s2, that is, if the set of possible priorities under
     * s1 is a subset of the set of possible priorities under s2 *)
    fun check_sub assign ctx (s1, s2) =
	let val _ = verbprint "starting check_sub\n"
	    val v = Variable.namedvar "prio__s"
	    val (rv1, rcs1, evs1, ecs1) = assign_in_prioset assign s1
	    val c1 = close_rfmt assign (IL.PVar v) (rv1, rcs1)
	    val (rv2, rcs2, evs2, ecs2) = assign_in_prioset assign s2
	    val _ = verbprint "s2:\n"
	    val _ = verb (fn () =>
			     Layout.print (ILPrint.pstol ([], RConcrete (rv2, rcs2)), print))
	    val c2 = close_rfmt assign (IL.PVar v) (rv2, rcs2)
	    val _ = verbprint "c2:\n"
	    val _ = verb (fn () => Layout.print
			(Layout.listex "" "" "," (map ILPrint.pctol c2), print))
	    val _ = verbprint "constraints in ctx\n"
	    val (ctx_evs, ctx_ecs) = constraints_in_ctx assign ctx (* XXX *)
  (* We want to assert ~(/\c1 => /\c2), which is the same as /\c1 /\ ~(/\c2) *)
	    val _ = verbprint "REALLY starting check_sub\n"
	in
	    if List.length c2 = 0 then
		(* s2 is T, so the implication is trivially satisfied *)
		true
	    else
		let val z3 =
			Z3.setup
			    NONE
			    (* (SOME (string_of_pconstraint (SOME assign) (PSSup (ctx, s2, s1)))) *)
			    ctx
			    ([v] @ evs1 @ evs2 @ ctx_evs)
		    val z3 =
			List.foldl
			    (fn (c, z3) => Z3.add_constraint (z3, c))
			    z3
			    (ctx_ecs @ ecs1 @ ecs2)
		    val z3 = Z3.add_comment (z3, "End ctx constraints\n")
		    val z3 =
			List.foldl
			    (fn (c, z3) => Z3.add_constraint (z3, c))
			    z3
			    c1
		    val z3 =
			(* Add the constraint ~(/\ c2)... *)
			Z3.add_negate_and_constraints (z3, c2)
		in
		    (* verbprint (z3); *)
		    (*... and check that the system is UNsatisfiable *)
		    not (Z3.check z3)
		end
	end

    fun priowf ctx evs dv (IL.PVar v) =
	V.eq (dv, v)
	orelse (List.exists (fn v' => V.eq (v', v)) evs)
	orelse
	((let val _ = Context.var_fail ctx (Variable.show v)
	  in true
	  end)
	 handle _ => false)
      | priowf ctx evs dv (IL.PConst s) =
	((let val _ = Context.var_fail ctx s
	  in true
	  end)
	 handle _ => false)
	    
    (* Check if ps is well-formed, i.e., has no unbound priority vars *)
    fun check_wf assign ctx ps =
	let val (rv, rcs, evs, _) = assign_in_prioset assign ps
	in
	    List.foldl
		(fn ((p1, p2), wf) =>
		    wf andalso
		    (priowf ctx evs rv p1) andalso (priowf ctx evs rv p2))
		true
		rcs
	end

    fun check assign constraint =
	let val _ = verb (fn () =>
			     (print "checking";
			      print (string_of_pconstraint NONE (*(SOME assign)*) constraint)))
		    
	    val sat = case type_of constraint of
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
		     NONE)
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
		SOME (n, IntMap.insert (assign, n, (rv, new_rcs)))
	    end

    fun weaken assign c =
	case type_of c of
	    PSSup (ctx, p1, p2) => weaken_sub assign ctx (p2, p1)
	  | PSWellformed (ctx, p) => weaken_wf assign ctx p
	  | PSCons _ => NONE

    (* Build an initial assignment for all of the RVars that show up in a
     * constraint, with the priorities that are in the context. *)	   
    fun assign_of_pconstraint desig_var c =
      let fun qualifiers_of_prios ctx ps =
	      let val all =
		      (List.map (fn p => (PVar desig_var, p)) ps)
		      @ (List.map (fn p => (p, PVar desig_var)) ps)
	      in
		  List.filter
		      (fn (p1, p2) =>
			  (case IL.prcompare (p1, p2) of
			       EQUAL => false
			     | _ =>  true
			  )
		      )
		      all
	      end
	  fun build_assign constraints rfmts =
	      List.foldl
		  (fn (RConcrete _, assign) => assign
		  | (RVar k, assign) =>
		    IntMap.insert (assign, k, (desig_var, constraints))
		  )
		  IntMap.empty
		  rfmts
	  fun qualifiers_of_ctx ctx =
	      let val ctxprios =
		      (List.map PVar (Context.prio_vars ctx))
		      @ (List.map PConst (Context.plabs ctx))
	      in
		  qualifiers_of_prios
		      ctx
		      ctxprios
	      end
      in
	   case type_of c of
	       PSCons (ctx, (_, r1), (_, r2)) =>
	       build_assign (qualifiers_of_ctx ctx) [r1, r2]
	     | PSSup (ctx, (_, r1), (_, r2)) =>
	       build_assign (qualifiers_of_ctx ctx) [r1, r2]
	     | PSWellformed (ctx, (_, r)) =>
	       build_assign (qualifiers_of_ctx ctx) [r]
      end

    fun partition pscstrs =
	List.foldl
	    (fn (c, (wf, sup, cons)) =>
		case type_of c of
		    PSSup _ => (wf, c::sup, cons)
		  | PSCons _ => (wf, sup, c::cons)
		  | PSWellformed _ => (c::wf, sup, cons)
	    )
	    ([], [], [])
	    pscstrs
		
end
