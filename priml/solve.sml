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
	      (* Take the cross product and then narrow it down with a
	       * couple sanity-check filters *)
	      let val all =
		      List.concat
			  (List.map
			       (fn p1 => List.map (fn p2 => (p1, p2)) ps)
			       ps
			  )
	      in
		  List.filter
		      (fn (p1, p2) =>
			  if Context.checkcons ctx p2 p1 then
			      (* If the constraint is clearly unsatisfiable,
				 remove it *)
			      false
			  else
			      (* If p1 = p2, remove the constraint *)
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
	      let val ctxprios = List.map PConst (Context.prios ctx)
	      in
		  qualifiers_of_prios
		      ctx
		      ((PVar desig_var)::ctxprios)
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
	  fun combine_assign ((dv, c1), (_, c2)) = (dv, c1 @ c2)
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
	  val assign =
	      (* First solve well-formedness constraints *)
	      List.foldl
	      (fn (PSWellformed (ctx, p), assign) =>
		  if check_wf assign ctx p then
		      assign
		  else
		      (case weaken_wf assign ctx p of
			   SOME assign => assign
			 | NONE => raise (Unsolvable (PSWellformed (ctx, p)))
		      )
	      )
	      assign
	      wf
	  fun solve_sup assign =
	      let val unsat = List.filter (fn c => (not (check assign c))) sup
		  val _ = verbprint ((Int.toString (List.length unsat)) ^ " unsat constraints\n")
	      in
		  case unsat of
		      [] => assign
		    | (PSSup (ctx, p1, p2))::unsat =>
		      let val _ = verbprint ("weakening " ^ (string_of_pconstraint (SOME assign) (PSSup (ctx, p1, p2))))
			  val assign =
			      case weaken_sub assign ctx (p2, p1) of
				  SOME assign => assign
				| NONE => raise (Unsolvable (PSSup (ctx, p1, p2)))
		      in
			  (* XXX TODO optimize this with the worklist optimization from the paper *)
			  solve_sup assign
		      end
	      end
	  val assign = solve_sup assign
      in
	  (* Now just check the priority-lessthan constraints *)
	  case List.filter (fn c => not (check assign c)) cons of
	      [] => (verbprint (string_of_assign assign); assign)
	    | c::_ => raise (Unsolvable c)
      end

end
