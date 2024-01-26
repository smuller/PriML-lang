structure Constraint =
struct

open IL
structure C = Context
structure V = Variable

exception Priority of string

fun mkpoly t = Poly ({tys = []}, t)

fun consval ctx v =
    case v of
	Polyvar {tys, var} =>
	(case C.var ctx (V.show var) of
	     (Poly (_, TPrio ps), _, _) =>
	     (TPrio (PSSet (PrioSet.singleton (PVar var))),
	      [])
	   | (Poly (_, t), _, _) =>
	     (t, [])
	)
      | Polyuvar {tys, var} =>
	(case C.var ctx (V.show var) of
	     (Poly (p, TPrio ps), _, _) =>
	     (TPrio (PSSet (PrioSet.singleton (PVar var))),
	      [])
	   | (Poly (_, t), _, _) =>
	     (t, [])
	)
      | MLVal _ => raise (Priority "what's an mlval?")
      | Int _ => (Initial.ilint, [])
      | String _ => (Initial.ilstring, [])
      | Prio p => (TPrio (PSSet (PrioSet.singleton p)), [])
      | VRecord fields =>
	let val (ts, ccs) =
	    List.foldl (fn ((l, v), (ts, ccs)) =>
			   let val (t, cs) = consval ctx v in
			       ((l, t)::ts, cs @ ccs)
			   end)
		       ([], [])
		       fields
	in
	    (TRec (List.rev ts), ccs)
	end
      | VRoll _ => raise (Priority "pretty sure this is unused")
      | VInject (t, cons, vopt) =>
	let val cs =
	    case vopt of
		SOME v => #2 (consval ctx v)
	      | NONE => []
	in
	    (t, cs)
	end
      | Fns fs =>
	let val ctx =
	    List.foldl
		(fn (f, ctx) =>
		    let val t =
			    mkpoly (Arrow (false,
					   ListPair.zip (#arg f, #dom f),
					   #cod f))
		    in
			C.bindv ctx (V.show (#name f)) t (#name f)
		    end
		)
		ctx
		fs
	in
	(Arrows (List.map (fn f => (false, ListPair.zip (#arg f, #dom f), #cod f)) fs),
	 List.concat
	     (List.map (fn f => #2 (cons ctx (#body f))) fs)
	)
	end
      | FSel (n, fs) =>
	(case consval ctx fs of
	     (Arrows ts, cs) => (Arrow (List.nth (ts, n)), cs)
	   | _ => raise (Priority "FSel value is not Fns")
	)
      | PCmd (p, t, cmd) =>
	let val (t, midprios, endprios, cs) = conscmd p ctx cmd in
	    (TCmd (t, (PSSet (PrioSet.singleton p), midprios, endprios)), cs)
	end
	    
and cons ctx e =
    case e of
	Value v => consval ctx v
      | _ => raise (Priority "not implemented")
	
and conscmd p ctx cmd =
    (TVar (V.newvar ()), PSSet (PrioSet.singleton p), PSSet (PrioSet.singleton p), [])

and consdec ctx d =
    raise (Priority "not implemented")

fun consprog (decs, prios, cons, fairness, maincmd) =
    let val (ctx, cs) =
	List.foldl
	    (fn (d, (ctx, cs)) =>
		 let val (ctx', cs') = consdec ctx d in
		     (ctx', cs @ cs')
		 end
	    )
	    (C.empty, [])
	    decs
	val (_, _, _, cs') = conscmd (PConst "bot") ctx maincmd
    in
	cs @ cs'
    end
	
end
