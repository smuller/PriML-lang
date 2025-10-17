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
	 

(* XXX solve constraints from cc *)
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
	  val assign = (* XXX TODO initial assignment *) IntMap.empty
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
	      let val unsat = List.filter
				  (fn c => not (check assign c))
				  sup
	      in
		  if List.length unsat = 0 then assign
		  else
		      let val assign = 
			      List.foldl
				  (fn (PSSup (ctx, p1, p2), assign) =>
				      (case weaken_sub assign ctx (p2, p1) of
					   SOME assign => assign
					 | NONE => raise (Unsolvable (PSSup (ctx, p1, p2))))
				  )
				  assign
				  unsat
		      in
			  (* XXX TODO optimize this with the worklist optimization from the paper *)
			  solve_sup assign
		      end
	      end
	  val assign = solve_sup assign
      in
	  (* Now just check the priority-lessthan constraints *)
	  case List.filter (fn c => not (check assign c)) cons of
	      [] => assign
	    | c::_ => raise (Unsolvable c)
      end

end
