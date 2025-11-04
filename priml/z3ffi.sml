structure Z3 :> PRIMLZ3 =
struct

type z3prio = MLton.Pointer.t
type z3ml = MLton.Pointer.t
	      
type z3 =
     { z3ml : z3ml, (* struct of Z3_context, Z3_solver *)
       prios : z3prio StringMap.map
     }

exception Z3 of string

val Z3ML_add_constraint = _import "Z3ML_add_constraint" : z3ml * z3prio * z3prio -> unit;
val Z3ML_add_negated_constraint = _import "Z3ML_add_negated_constraint" : z3ml * z3prio * z3prio -> unit;
val Z3ML_make_context_and_solver =_import "Z3ML_make_context_and_solver" : unit -> z3ml;
val Z3ML_add_distinct =_import "Z3ML_add_distinct" : z3ml * z3prio array * int -> unit;
val Z3ML_add_constant = _import "Z3ML_add_constant" : z3ml * string -> z3prio;
val Z3ML_add_one_of = _import "Z3ML_add_one_of" : z3ml * z3prio * z3prio array * int -> unit;
val Z3ML_add_negate_and_constraints = _import "Z3ML_add_negate_and_constraints" : z3ml * z3prio array * int -> unit;
val Z3ML_check = _import "Z3ML_check" : z3ml -> bool;

fun string_of_prio p =
    case p of
	IL.PVar v => Variable.show v
      | IL.PConst s => s

fun zero_term s =
    s ^ (String.implode [Char.chr 0])

fun lookup_prio_by_string z3 s =
    case StringMap.find (#prios z3, s) of
	NONE => raise (Z3 ("prio not found: " ^ s))
      | SOME prio => prio

fun lookup_prio z3 p =
    let val s = string_of_prio p
    in
	lookup_prio_by_string z3 s
    end
    
fun add_constraint (z3, (p1, p2)) =
    (Z3ML_add_constraint (#z3ml z3, lookup_prio z3 p1, lookup_prio z3 p2);
     z3)

fun add_negated_constraint (z3, (p1, p2)) =
    (Z3ML_add_negated_constraint (#z3ml z3, lookup_prio z3 p1, lookup_prio z3 p2);
     z3)

fun add_comment (z3, s) =
    z3

val notleppairs = ref []
	
fun setup constraint ctx extra_vars =
    let val orders = Context.pcons ctx
	val prios = (Context.prio_vars ctx) @ extra_vars
	val plabs = Context.plabs ctx
	val notleppairs =
	    case !notleppairs of
		[] => 
		let val priopairs =
			List.concat
			    (List.map
				 (fn p1 => List.map (fn p2 => (IL.PConst p1, IL.PConst p2)) plabs)
				 plabs)
		    val pairs =
			List.filter
			    (fn (p1, p2) =>
				not (Context.checkcons ctx p1 p2)
			    )
			    priopairs
		in
		    pairs
		    before notleppairs := pairs
		end
	      | pairs => (verbprint "reusing notleppairs\n"; pairs)
	val priomap = StringMap.empty
	val _ = verbprint "setting up context\n"
	val z3 = Z3ML_make_context_and_solver ()
	val _ = verbprint "done\nmaking constants\n"
	val priomap =
	    List.foldl
		(fn (k, prios) =>
		    let val s = Variable.show k
		    in
			StringMap.insert (prios, s,
					  Z3ML_add_constant (z3, zero_term s))
		    end
		)
		priomap
		prios
	val priomap =
	    List.foldl
		(fn (s, prios) =>
		    StringMap.insert (prios, s,
				      Z3ML_add_constant (z3, zero_term s))
		)
		priomap
		plabs
	val _ = verbprint "done\n"
	val z3 =
	    {z3ml = z3,
	     prios = priomap}
	val plab_array =
	    Array.tabulate
		(List.length plabs,
		 (fn i => lookup_prio_by_string z3 (List.nth (plabs, i))))
	val _ = verbprint "adding distinct\n";
	val _ = Z3ML_add_distinct (#z3ml z3,
				   plab_array,
				   Array.length plab_array)
	val _ = verbprint "adding one-of\n"
	val _ = List.app
		(fn pvar =>
		    Z3ML_add_one_of (#z3ml z3,
				     lookup_prio_by_string z3 (Variable.show pvar),
				     plab_array,
				     Array.length plab_array))
		prios
	val _ = verbprint "adding constraints\n"
	val _ = List.app
		    (fn c => ignore (add_constraint (z3, c)))
		    orders
	val _ = List.app
		    (fn c => ignore (add_negated_constraint (z3, c)))
		    notleppairs
    in
	verbprint "done with setup\n";
	z3
    end


fun add_negate_and_constraints ((z3, ps) : z3 * (IL.pconstraint list)) =
    let val arrlen = List.length ps * 2
	val arr = Array.tabulate
		  (arrlen,
		   (fn i =>
		       let val (n, s) =
			       (i div 2, if i mod 2 = 0 then #1 else #2)
		       in
			   lookup_prio z3 (s (List.nth (ps, n)))
		       end
		   )
		  )
	val {z3ml, prios} = z3
    in
	Z3ML_add_negate_and_constraints (z3ml, arr, arrlen);
	z3
    end

val z3calls = ref 0
val z3time = ref 0
	     
fun check {z3ml, prios} =
    let val timer = Timer.startRealTimer ()
	val res = Z3ML_check z3ml
	val endtime = Timer.checkRealTimer timer
    in
	z3calls := (!z3calls) + 1;
	z3time := (!z3time) + (Time.toMicroseconds endtime);
	res
    end

end
