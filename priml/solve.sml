structure Solve =
struct

  structure V = Variable
  structure C = Context
  structure PSC = PSContext
  structure E = EL

  open IL
  open ElabUtil
  open PSetCstrs
  open Constraint
  structure P = Primop
	 

(* XXX solve constraints from cc *)
fun solve_psetcstrs pscstrs = 
    let val psctx = PSC.PSEvarMap.empty
	val _ =
	    Layout.print
                (Layout.listex "[" "]" "," 
			       (map PSetCstrs.psctol pscstrs), print)
        val psctx_sol = solve_pscstrs psctx pscstrs
    in
        (* check psevar solution satifies every psconstraints *)
        check_pscstrs_sol psctx_sol pscstrs;
        Layout.print 
            (Layout.listex "[" "]" "," 
            (PSC.PSEvarMap.listItems (PSC.PSEvarMap.mapi 
					  (fn (k, ps) => Layout.seq [ILPrint.pstol k, Layout.listex ": {" "} " "," (map ILPrint.prtol (PrioSet.listItems ps))]) 
					  (psctx_sol))), 
             print);
        print "\n"
    end
    handle PSConstraints s =>
	   (print s; raise Elaborate ("psconstraint solver: " ^ s))

end
