structure Z3 :> PRIMLZ3 =
struct

structure SS = StringSet

type z3 = string

exception Z3 of string

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

fun comment s =
    if !verbose then
	"; " ^ (String.translate (fn #"\n" => "\n; "
				   | c => String.implode [c]) s) ^ "\n"
    else ""
    
fun setup constraint ctx extra_vars =
    let val orders = Context.pcons ctx
	fun insert_into_set (p, prios) =
	    SS.add (prios, string_of_prio p)
	fun insert_order ((p1, p2), prios) =
	    insert_into_set (p1, insert_into_set (p2, prios))
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
	    
    in
	(case constraint of
	     SOME s => comment s
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
    end

fun compose (z1, z2) = z1 ^ z2


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

val z3calls = ref 0
val z3time = ref 0

fun check z3 =
    let val z3 = z3 ^ "(check-sat)"
	val tempfile = "z3temp.smt"
	val outfile = "z3out"
	val os = TextIO.openOut tempfile
	val _ = TextIO.output (os, z3)
	val _ = TextIO.closeOut os
	val z3cmd = "z3"
	val timer = Timer.startRealTimer ()
	val status = OS.Process.system (z3cmd ^ " " ^ tempfile ^ " > " ^ outfile)
	val endtime = Timer.checkRealTimer timer
	val is = TextIO.openIn outfile
	val ret = TextIO.inputLine is
	val _ = TextIO.closeIn is
    in
	z3calls := (!z3calls) + 1;
	z3time := (!z3time) + (Time.toMilliseconds endtime);
	if OS.Process.isSuccess status then
	    case ret of
		NONE => raise (Z3 "unknown Z3 return value")
	      | SOME s =>
		(let val b = String.isPrefix "sat" s in
		     b
		 end)
	else
	    raise (Z3 "Z3 returned error")
    end

end
	
		   
