structure Solve =
struct

  structure V = Variable
  structure C = Context
  structure E = EL

  open IL
  open ElabUtil
  open PSetCstrs
  open Constraint
  structure P = Primop

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
	   case c of
	       PSCons (ctx, (_, r1), (_, r2)) =>
	       build_assign (qualifiers_of_ctx ctx) [r1, r2]
	     | PSSup (ctx, (_, r1), (_, r2)) =>
	       build_assign (qualifiers_of_ctx ctx) [r1, r2]
	     | PSWellformed (ctx, (_, r)) =>
	       build_assign (qualifiers_of_ctx ctx) [r]
      end

  fun solve_psetcstrs pscstrs =
      (* First separate the constraints by type *)
      let val (wf, sup, cons) =
	      List.foldl
	      (fn (c, (wf, sup, cons)) =>
		  case c of
		      PSSup _ => (wf, c::sup, cons)
		    | PSCons _ => (wf, sup, c::cons)
		    | PSWellformed _ => (c::wf, sup, cons)
	      )
	      ([], [], [])
	      pscstrs
	  val desig_var = V.namedvar "__v"
	  fun combine_assign ((dv, c1), (_, c2)) =
	      (dv,
	       (List.filter (fn (p1, p2) =>
				not (List.exists
					 (fn (p1', p2') =>
					     IL.prcompare (p1, p1') = EQUAL
					     andalso IL.prcompare (p2, p2') = EQUAL)
					 c2)
			    )
			    c1) @ c2)
	  val assign = (* initial assignment *)
	      List.foldl
		  (fn (c, assign) =>
		       IntMap.unionWith
			   combine_assign
			   (assign_of_pconstraint desig_var c,
			    assign)
		  )
		  IntMap.empty
		  pscstrs
	  val _ = verbprint "Checking wf constraints\n"
	  val assign =
	      (* First solve well-formedness constraints *)
	      List.foldl
	      (fn (PSWellformed (ctx, p), assign) =>
		  if check assign (PSWellformed (ctx, p)) then
		      assign
		  else
		      (case weaken_wf assign ctx p of
			   SOME assign => assign
			 | NONE => raise (Unsolvable (PSWellformed (ctx, p)))
		      )
	      )
	      assign
	      wf
	  val _ = verbprint "Done with wf constraints\n"
	  fun solve_sup assign maybe_unsat curr_sat =
	      let val _ = verbprint "CURRENT ASSIGNMENT:\n"
		  val _ = verbprint (string_of_assign assign)
		  val (now_sat, still_unsat) =
		      List.partition (fn c => check assign c) maybe_unsat
		  val _ =
		      verbprint
			  ((Int.toString (List.length still_unsat))
			   ^ " unsat constraints\n")
	      in
		  case still_unsat of
		      [] => assign
		    | (PSSup (ctx, p1, p2))::rest_unsat =>
		      let val _ = verbprint ("weakening " ^ (string_of_pconstraint (SOME assign) (PSSup (ctx, p1, p2))))
			  val (changed, assign) =
			      case weaken_sub assign ctx (p2, p1) of
				  SOME assign => assign
				| NONE => raise (PSConstraints (string_of_pconstraint (SOME assign) (PSSup (ctx, p1, p2))))
(* Constraints to check on the next round are those that were unsat
 * before and those whose context or antecedent changed *)
			  val (changed_cons, unchanged_cons) =
			      List.partition
				  (fn (PSSup (ctx, _, (_, (RVar n)))) =>
				      n = changed
				      orelse Context.has_rfmtvar ctx changed
				    | (PSSup (ctx, _, _)) =>
				      Context.has_rfmtvar ctx changed
				    | _ => false)
			      (now_sat @ curr_sat)
		      in
			  solve_sup assign (rest_unsat @ changed_cons) unchanged_cons
		      end
	      end
	  val assign = solve_sup assign sup []
      in
	  (* Now just check the priority-lessthan constraints *)
	  case List.filter (fn c => not (check assign c)) cons of
	      [] => (verbprint (string_of_assign assign); assign)
	    | c::_ => raise (PSConstraints (string_of_pconstraint (SOME assign) c))
      end

end
