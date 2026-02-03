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


  fun solve_psetcstrs pscstrs =
      (* First separate the constraints by type *)
      let val solvetimer = Timer.startRealTimer ()
	  val (wf, sup, cons) = partition pscstrs
	      
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
	  val after_init = Timer.checkRealTimer solvetimer
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
	  val after_wf = Timer.checkRealTimer solvetimer
	  val _ = verbprint "Done with wf constraints\n"
	  fun solve_sup assign maybe_unsat curr_sat =
	      let val _ = verbprint "CURRENT ASSIGNMENT:\n"
		  val _ = verb (fn () => print (string_of_assign assign))
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
		      let val _ = verb (fn () => print ("weakening " ^ (string_of_pconstraint (SOME assign) (PSSup (ctx, p1, p2)))))
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
	  val after_sup = Timer.checkRealTimer solvetimer
	  val res =
	      (* Now just check the priority-lessthan constraints *)
	      case List.filter (fn c => not (check assign c)) cons of
		  [] => (verb (fn () => print (string_of_assign assign)); assign)
		| c::_ => raise (PSConstraints (string_of_pconstraint (SOME assign) c))
	  val after_lt = Timer.checkRealTimer solvetimer
      in
	   print ("Init time (us):\t" ^ (LargeInt.toString
					     (Time.toMicroseconds after_init))
		  ^ "\n");
	   print ("WF time (us):\t" ^ (LargeInt.toString
					   ((Time.toMicroseconds after_wf)
					    - (Time.toMicroseconds after_init)))
		  ^ "\n");
	   print ("Imp time (us):\t" ^ (LargeInt.toString
					   ((Time.toMicroseconds after_sup)
					    - (Time.toMicroseconds after_wf)))
		  ^ "\n");
	   print ("LE time (us):\t" ^ (LargeInt.toString
					   ((Time.toMicroseconds after_lt)
					    - (Time.toMicroseconds after_sup)))
		  ^ "\n");
	   res
      end
end
