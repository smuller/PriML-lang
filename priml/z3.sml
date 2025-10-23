structure Z3 :> PRIMLZ3 =
struct

structure SS = StringSet

type z3 = string

exception Z3 of string

fun string_of_prio p =
	    case p of
		IL.PVar v => Variable.show v
	      | IL.PConst s => s

fun of_constraint (p1, p2) =
    "(assert (LT " ^ (string_of_prio p1) ^ " "
    ^ (string_of_prio p2) ^ "))\n"

fun setup constraint ctx extra_vars =
    let val orders = Context.pcons ctx
	fun insert_into_set (p, prios) =
	    SS.add (prios, string_of_prio p)
	fun insert_order ((p1, p2), prios) =
	    insert_into_set (p1, insert_into_set (p2, prios))
	val prios = (Context.prios ctx) @ (List.map Variable.show extra_vars)
	val plabs = Context.plabs ctx
(*	    List.foldl
		insert_order
		SS.empty
		orders
*)
    in
	(case constraint of
	     SOME s =>
	     "; " ^ (String.translate (fn #"\n" => "\n; "
				      | c => String.implode [c]) s) ^ "\n"
	  |  NONE => "")
	^ "(declare-sort Prio 0)\n"
	^ "(define-fun LT ((x Prio) (y Prio)) Bool ((_ partial-order 0) x y))\n"
	^
	(List.foldl
	     (fn (k, s) =>
		  s ^ "(declare-const " ^ k ^ " Prio)\n"
	     )
	     ""
	     prios
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
	^
	(String.concat (List.map of_constraint orders))
    end

fun compose (z1, z2) = z1 ^ z2

fun negate_constraint (p1, p2) =
    "(assert (not (LT " ^ (string_of_prio p1) ^ " "
    ^ (string_of_prio p2) ^ ")))\n"

fun negate_and_constraints ps =
    "(assert (not (and "
    ^
    String.concatWith " "
		      (List.map (fn (p1, p2) =>
				    "(LT " ^ (string_of_prio p1) ^ " "
				    ^ (string_of_prio p2) ^ ")")
				ps
		      )
    ^ ")))\n"

fun check z3 =
    let val tempfile = "z3temp.smt"
	val os = TextIO.openOut tempfile
	val _ = TextIO.output (os, z3)
	val _ = TextIO.closeOut os
	val z3cmd = "z3"
	val status = OS.Process.system (z3cmd ^ " " ^ tempfile)
    in
	not (OS.Process.isSuccess status)
    end

end
	
		   
