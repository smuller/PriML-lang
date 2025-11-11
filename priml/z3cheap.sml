structure Z3 :> PRIMLZ3 =
struct


structure C = Context
type z3 = string * C.context * IL.pconstraint list

exception Z3 of string

val Z3ML_check_string = _import "Z3ML_check_string" : string -> bool;

fun string_of_prio p =
	    case p of
		IL.PVar v => Variable.basename v
	      | IL.PConst s => s

fun of_constraint (p1, p2) =
    "(assert (LT " ^ (string_of_prio p1) ^ " "
    ^ (string_of_prio p2) ^ "))\n"

fun negate_constraint (p1, p2) =
    "(assert (not (LT " ^ (string_of_prio p1) ^ " "
    ^ (string_of_prio p2) ^ ")))\n"

fun add_constraint ((z3, ctx, cons), (p1, p2)) =
    (z3 ^ (of_constraint (p1, p2)),
     C.bindplecons ctx (p1, p2), cons)

fun add_negated_constraint ((z3, ctx, cons), (p1, p2)) =
    (z3 ^ (negate_constraint (p1, p2)),
     ctx, (p1, p2)::cons)

fun add_comment ((z3, ctx, cons), s) =
    (z3 ^
    (if !verbose then
	 "; " ^ (String.translate (fn #"\n" => "\n; "
				    | c => String.implode [c]) s) ^ "\n"
     else ""),
     ctx, cons)
    
fun setup constraint ctx extra_vars =
    let val orders = Context.pcons ctx
	val prios = (Context.prio_vars ctx) @ extra_vars
	val plabs = Context.plabs ctx
(*	    List.foldl
		insert_order
		SS.empty
		orders
 *)
	val priopairs =
	    List.concat
	    (List.map
		 (fn p1 => List.map (fn p2 => (IL.PConst p1, IL.PConst p2)) plabs)
		 plabs)
	val notleppairs =
	    List.filter
	    (fn (p1, p2) =>
		not (Context.checkcons ctx p1 p2)
	    )
	    priopairs
	val ctx_with_prios =
	    List.foldl
		(fn (v, ctx) => C.bindplab ctx (Variable.basename v))
		C.empty
		prios
	val ctx_with_prios =
	    List.foldl
		(fn (k, ctx) => C.bindplab ctx k)
		C.empty
		plabs
	val ctx =
	    List.foldl
		(fn (cons, c) => C.bindpcons c cons)
		ctx_with_prios
		orders
    in
	(
	(case constraint of
	     SOME s =>
	     if !verbose then
		 "; " ^ (String.translate (fn #"\n" => "\n; "
					  | c => String.implode [c]) s) ^ "\n"
	     else ""
	   |  NONE => "")
	^ "(declare-sort Prio 0)\n"
	^ "(define-fun LT ((x Prio) (y Prio)) Bool ((_ partial-order 0) x y))\n"
	^
	(List.foldl
	     (fn (k, s) =>
		  s ^ "(declare-const " ^ (Variable.basename k) ^ " Prio)\n"
	     )
	     ""
	     prios
	)
	^
	(List.foldl
	     (fn (k, s) =>
		  s ^ "(declare-const " ^ k ^ " Prio)\n"
	     )
	     ""
	     plabs
	)
	^ "(assert (distinct"
	^
	(List.foldl
	     (fn (k, s) =>
		  s ^ " " ^ k
	     )
	     ""
	     plabs
	)
	^ "))\n"
	^ (String.concat
	       (List.map
	   (fn pvar =>
	       "(assert (or "
	       ^ (String.concatWith
		    " "
		    (List.map (fn plab => "(= " ^ (Variable.basename pvar) ^ " " ^ plab ^ ")") plabs)
	       ) ^ "))\n"
	   )
	   prios
	  ))
	^ (String.concat (List.map of_constraint orders))
	^ (String.concat (List.map negate_constraint notleppairs))
	^ "\n; END SETUP\n"
	, ctx, [])
    end

fun add_negate_and_constraints ((z3, ctx, cons), ps) =
    (z3
    ^ "(assert (not (and "
    ^
    String.concatWith " "
		      (List.map (fn (p1, p2) =>
				    "(LT " ^ (string_of_prio p1) ^ " "
				    ^ (string_of_prio p2) ^ ")")
				ps
		      )
    ^ ")))\n",
     ctx, ps @ cons)

val z3calls = ref 0
val z3time = ref 0

fun check (z3, ctx, cons) =
    let val from_ctx =
	    List.all
		(fn (p1, p2) => C.checkcons ctx p1 p2)
		cons
    in
	if from_ctx then false
	else
    let val z3 = z3 ^ "(check-sat)" ^ (String.implode [Char.chr 0])
	val _ = verbprint "checking\n"
	val _ = verbprint (z3 ^ "\n")
	val timer = Timer.startRealTimer ()
	val ret = Z3ML_check_string z3
	val endtime = Timer.checkRealTimer timer
    in
	z3calls := (!z3calls) + 1;
	z3time := (!z3time) + (Time.toMicroseconds endtime);
	ret
    end
    end

end
	
		   
