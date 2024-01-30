structure Constraint =
struct

open IL
structure C = Context
structure V = Variable

open PSetCstrs
     
exception PriorityErr of string
exception TyError of string

fun mkpoly t = Poly ({tys = []}, t)

val new_psevar = Unify.new_psevar

fun basety (t, cs) =
    case t of
	(Evar (ref (Bound t))) => basety (t, cs)
      | _ => (t, cs)

fun supertypex ctx t1 t2 =
    let val _ = Layout.print (Layout.listex
				  "supertype (" ")\n" ","
				  (map ILPrint.ttol [t1, t2]),
			      print)
    in
        (case (t1, t2) of
             (TVar v1, TVar v2) => []
           | (TTag (t1, v1), TTag (t2, v2)) => 
             supertypex ctx t1 t2
           | (TVec t1, TVec t2) => supertypex ctx t1 t2
           | (TCont t1, TCont t2) => supertypex ctx t1 t2
           | (TRec lcl1, TRec lcl2) =>
             let
                 val l = ListUtil.sort 
                             (ListUtil.byfirst String.compare) lcl1
                 val r = ListUtil.sort 
                             (ListUtil.byfirst String.compare) lcl2
		 val cs = ListPair.map
			      (fn ((_, t1), (_, t2)) =>
				  supertypex ctx t1 t2)
			      (l, r)
             in
		 List.concat cs
	     end
           | (Arrow (_, dom1, cod1), Arrow (_, dom2, cod2)) => 
             let
		 val domcs = ListPair.map
			      (fn ((_, a), (_, b)) =>
				  supertypex ctx b a
					     (* FIX: domain is contravariant *)
			      )
                              (dom1, dom2)

		 val codcs = supertypex ctx cod1 cod2
	     in
		 List.concat (codcs::domcs)
             end
           | (TRef c1, TRef c2) => supertypex ctx c1 c2
           | (Mu (_, m1), Mu (_, m2)) => 
             let val cs = ListPair.map (fn ((_, t1), (_, t2)) =>
					   supertypex ctx t1 t2)
				       (m1, m2)
	     in
		 List.concat cs
	     end
           | (Sum ltl1, Sum ltl2) =>
	     let val cs = ListPair.map
			      (fn ((_, t1), (_, t2)) =>
				  case (t1, t2) of
                                      (NonCarrier, NonCarrier) => []
                                    | (Carrier { definitely_allocated = aa1, carried = tt1}, 
                                       Carrier { definitely_allocated = aa2, carried = tt2}) => 
                                            supertypex ctx tt1 tt2
                                    | _ => raise TyError "sum:carrier")
			      (ListUtil.sort (ListUtil.byfirst String.compare) ltl1,
			       ListUtil.sort (ListUtil.byfirst String.compare) ltl2)
	     in
		 List.concat cs
	     end
           | (Arrows al1, Arrows al2) =>
             if length al1 <> length al2 then
		 raise TyError "Arrows have different arity"
             else
		 let val cs =
			 ListPair.map
			     (fn ((_, dom1, cod1), (_, dom2, cod2)) =>
				 List.concat
				     (
				      (supertypex ctx cod1 cod2)::
                                 (ListPair.map
				     (fn ((_, a), (_, b)) =>
					 supertypex ctx b a
						    (* FIX: domain is contravariant *)
				     )
				     (dom1, dom2)
			     )))
			     (al1, al2)
		 in
		     List.concat cs
		 end
           | (TCmd (t1, (pi1, pp1, pf1)), TCmd (t2, (pi2, pp2, pf2))) =>
               (pscstr_sup ctx pi2 pi1) (* FIX: start refinement contravariant *)
               @ (pscstr_sup ctx pp1 pp2)
               @ (pscstr_sup ctx pf1 pf2)
	       @ (supertypex ctx t1 t2)
           | (TThread (t1, ps1), TThread (t2, ps2)) =>
	     (pscstr_sup ctx ps1 ps2) @ (supertypex ctx t1 t2)
           | (TPrio ps1, TPrio ps2) => pscstr_sup ctx ps1 ps2
	   | (Evar (ref (Bound t1)), Evar (ref (Bound t2))) =>
	     supertypex ctx t1 t2
	   | (Evar (ref (Bound t1)), t2) => supertypex ctx t1 t2
	   | (t1, Evar (ref (Bound t2))) => supertypex ctx t1 t2
	   | (Evar (ref (Free _)), _) => []
	   | (_, Evar (ref (Free _))) => []
	   | _ => raise (TyError ("supertype unhandled case"
				  ^
				  (Layout.tostring
				    (Layout.listex
					 "supertype (" ")\n" ","
					 (map ILPrint.ttol [t1, t2]))
				 )))
	)
    end

fun subtype ctx t1 t2 =
    (supertypex ctx t2 t1)
    handle TyError s => (print s; raise (TyError s))
	
fun wf_cons ctx t =
    case t of
	TVar _ => []
      | TRec fields =>
	List.concat (List.map (fn (_, t) => wf_cons ctx t) fields)
      | Arrow (_, dom, cod) =>
	let val dom_cons = List.map (fn (_, t) => wf_cons ctx t) dom
	in
	    (wf_cons ctx cod) @ (List.concat dom_cons)
	end
      | Sum arms =>
	List.concat (List.map (fn (_, ai) =>
				  case ai of NonCarrier => []
					   | Carrier {carried, ...} =>
					     wf_cons ctx carried
			      )
			      arms)
      | Mu (i, typs) =>
	List.concat (List.map (fn (_, t) => wf_cons ctx t) typs)
      | Evar _ => []
      | TVec t => wf_cons ctx t
      | TCont t => wf_cons ctx t
      | TRef t => wf_cons ctx t
      | TTag (t, _) => wf_cons ctx t
      | Arrows fns =>
	List.concat
	    (List.map
		 (fn (_, dom, cod) =>
		     let val dom_cons = List.map (fn (_, t) => wf_cons ctx t) dom
		     in
			 (wf_cons ctx cod) @ (List.concat dom_cons)
		     end
		 )
		 fns
	    )
      | TCmd (t, (p1, p2, p3)) =>
	(pscstr_wf ctx p1)
	@ (pscstr_wf ctx p2)
	@ (pscstr_wf ctx p3)
	@ (wf_cons ctx t)
      | TThread (t, p) => (pscstr_wf ctx p) @ (wf_cons ctx t)
      | TPrio p => (pscstr_wf ctx p)

fun fresh t =
    case t of
	TVar _ => t
      | TRec fields =>
	TRec (List.map (fn (l, t) => (l, fresh t)) fields)
      | Arrow (total, dom, cod) =>
	Arrow (total,
	       List.map (fn (x, t) => (x, fresh t)) dom,
	       fresh cod)
      | Sum arms =>
	Sum (List.map (fn (l, ai) => (l, arminfo_map fresh ai)) arms)
      | Mu (i, typs) =>
	Mu (i, List.map (fn (x, t) => (x, fresh t)) typs)
      | Evar _ => t
      | TVec t => TVec (fresh t)
      | TCont t => TCont (fresh t)
      | TRef t => TRef (fresh t)
      | TTag (t, v) => TTag (fresh t, v)
      | Arrows fns =>
	Arrows
	(List.map (fn (total, dom, cod) =>
		      (total,
		       List.map (fn (x, t) => (x, fresh t)) dom,
		       fresh cod)
		  )
		  fns)
      | TCmd (t, (_, _, _)) =>
	TCmd (fresh t, (new_psevar (), new_psevar (), new_psevar ()))
      | TThread (t, _) => TThread (fresh t, new_psevar ())
      | TPrio _ => TPrio (new_psevar ())

fun consval ctx v =
    let val _ = Layout.print (Layout.mayAlign [Layout.str "consval ",
					       ILPrint.vtol v,
					       Layout.str "\n"], print) in
    case v of
	Polyvar {tys, var} =>
	let val (t, cs) =
	(case C.var ctx (V.show var) of
	     (Poly (_, TPrio ps), _, _) =>
	     (TPrio (PSSet (PrioSet.singleton (PVar var))),
	      [])
	   | (Poly (_, t), _, _) =>
	     (t, [])
	)
	in
	    Layout.print (Layout.mayAlign [Layout.str "type of ",
					   Layout.str (V.show var),
					   Layout.str ": ",
					   ILPrint.ttol t],
			  print);
	    (t, cs)
	end
      | Polyuvar {tys, var} =>
	let val (t, cs) =
	(case C.var ctx (V.show var) of
	     (Poly (_, TPrio ps), _, _) =>
	     (TPrio (PSSet (PrioSet.singleton (PVar var))),
	      [])
	   | (Poly (_, t), _, _) =>
	     (t, [])
	)
	in
	    Layout.print (Layout.mayAlign [Layout.str "type of ",
					   Layout.str (V.show var),
					   Layout.str ": ",
					   ILPrint.ttol t],
			  print);
	    (t, cs)
	end
      | MLVal _ => raise (PriorityErr "what's an mlval?")
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
      | VRoll _ => raise (PriorityErr "pretty sure this is unused")
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
	   | _ => raise (PriorityErr "FSel value is not Fns")
	)
      | PCmd (p, t, cmd) =>
	let val (t, midprios, endprios, cs) = conscmd p ctx cmd in
	    (TCmd (t, (p, midprios, endprios)), cs)
	end
end
	    
and cons ctx e : typ * (psconstraint list) =
    let val _ = Layout.print (Layout.mayAlign [Layout.str "cons ",
					       ILPrint.etol e,
					       Layout.str "\n"], print) in
    case e of
	Value v => consval ctx v
      | App (efun, eargs) =>
	let val (funty, cs) = cons ctx efun
	    val (argtys, css) = ListPair.unzip (List.map (cons ctx) eargs)
	in
	    case funty of
		Arrow (_, dom, cod) =>
		let val subcs = ListPair.map
				    (fn (argty, (_, party)) =>
					subtype ctx argty party)
				    (argtys, dom)
		    val substs = ListPair.map (fn ((x, _), arg) => (x, arg))
					      (dom, eargs)
		in
		    (Subst.subst_e_in_t (Subst.fromlist substs) cod,
		     List.concat (cs::(css @ subcs)))
		end
	end
      | Record fields =>
	let val (ts, ccs) =
		List.foldl (fn ((l, v), (ts, ccs)) =>
			       let val (t, cs) = cons ctx v in
				   ((l, t)::ts, cs @ ccs)
			       end)
			   ([], [])
			   fields
	in
	    (TRec (List.rev ts), ccs)
	end
      | Proj (label, t, e) =>
	let val field_t =
		case t of
		    TRec fields =>
		    (case List.filter (fn (l, _) => l = label) fields of
			 (_, t)::_ => t
		       | _ => raise (TyError "field not found")
		    )
		  | _ => raise (TyError "not a record type")
	    val (et, cs) = cons ctx e
	in
	    (field_t, (subtype ctx et field_t) @ cs)
	end
      | Raise (t, e) =>
	let val (_, cs) = cons ctx e in
	    (t, cs)
	end
	
      (* var bound to exn value within handler*)
      | Handle (ebody, t, evar, handler) =>
	let val (_, cs1) = cons ctx ebody
	    val ctx' = C.bindv ctx (V.show evar) (mkpoly Initial.ilexn) evar
	    val (_, cs2) = cons ctx' handler
	in
	    (t, cs1 @ cs2)
	end

      | Seq (e1, e2) =>
	let val (_, cons1) = cons ctx e1
	    val (t2, cons2) = cons ctx e2
	in
	    (t2, cons1 @ cons2)
	end

      | Let (d, ebody, t) => 
	let val F = fresh t
	    val (ctx', subs, cs) = consdec ctx d
	    val (F2, cs') = cons ctx' ebody
	    val _ = print "subtype let\n"
	    val subcs = subtype ctx' F2 F
	in
	    (Subst.subst_e_in_t (Subst.fromlist subs) F,
	     cs @ cs' @ subcs @ (wf_cons ctx F))
	end
	    
      | Unroll e =>
	(case basety (cons ctx e) of
	     (Mu (n, arms), cs) =>
	     let val subst = Subst.fromlist
			     (List.tabulate
			      (List.length arms,
			       (fn i =>
				   let val (v, t) = List.nth (arms, i) in
				       (v, Mu (i, arms))
				   end
			       )
			     ))
	     in
		 (Subst.tsubst subst (#2 (List.nth (arms, n))), cs)
	     end
	   | _ => raise (TyError "not a Mu")
	)

      | Roll (t, e) =>
	let val (_, cs) = cons ctx e in
	    (t, cs)
	end

      (* tag v with t *)
      | Tag (e, et) => (TRec [], []) (* XXX *)

      | Untag _ => (TRec [], []) (* XXX *)

      (* apply a primitive to some expressions and types *)
      | Primapp (po, eargs, argtys) =>
	let
            val { worlds, tys, dom, cod } = Podata.potype po
	    val (_, cs) = ListPair.unzip
			      (List.map (cons ctx) eargs)
	in
	    (TRec [] (* XXX *), List.concat cs)
	end

      (* sum type, object, var (for all arms but not default), 
         branches, default, return type.
         the label/exp list need not be exhaustive.
         *)
      | Sumcase (sumty, ecase, branchvar, branches, def, rett) =>
	let val constrs =
		case sumty of
		    Sum ts => ts
		  | _ => raise (TyError "not a sum type")
	    val F = fresh rett
	    val (_, cs) = cons ctx ecase
	    val (tys, css) =
		ListPair.unzip
		    (ListPair.map
			 (fn ((_, e), (_, arm)) =>
			     let val ctx' =
				     case arm of
					 NonCarrier => ctx
				       | Carrier {carried, ...} =>
					 C.bindv ctx
					       (V.show branchvar)
					       (mkpoly carried)
					       branchvar
			     in
				 cons ctx' e
			     end)
			 (branches, constrs))
	    val (dty, dcs) = cons ctx def
	    val subtycs =
		List.concat
		    (List.map (supertypex ctx F) (dty::tys))
	in
	    (F, cs @ dcs @ subtycs @ (wf_cons ctx F) @ (List.concat css))
	end

      (* simpler; no inner val needs to be defined. can't be exhaustive. *)
      | Intcase (ecase, branches, def, rett) =>
	let val F = fresh rett
	    val (_, cs) = cons ctx ecase
	    val (tys, css) =
		ListPair.unzip
		    (List.map (fn (_, e) => cons ctx e) branches)
	    val (dty, dcs) = cons ctx def
	    val subtycs =
		List.concat
		    (List.map (supertypex ctx F) (dty::tys))
	in
	    (F, cs @ dcs @ subtycs @ (wf_cons ctx F) @ (List.concat css))
	end

	
      | Inject (t, label, eopt) =>
	(case eopt of
	     NONE => (t, [])
	   | SOME e =>
	     let val (_, cs) = cons ctx e
	     in
		 (t, cs)
	     end
	)
	
      | Cmd (p, cmd) =>
	let val (t, midprios, endprios, cs) = conscmd p ctx cmd
	in
	    (TCmd (t, (p, midprios, endprios)),
	     cs)
	end
    end
	
and conscmd sp ctx cmd =
    let val _ = Layout.print (Layout.mayAlign [Layout.str "cons ",
					       ILPrint.ctol cmd,
					       Layout.str "\n"], print) in
    case cmd of
	Bind (x, e, m) =>
	(case basety (cons ctx e) of
	     (TCmd (t, (startprios, midprios, endprios)), cs) =>
	     let val ctx' = C.bindv ctx (V.show x) (mkpoly t) x
		 val p = new_psevar ()
		 val (t', mp', ep', cs') = conscmd endprios ctx' m
	     in
		 (t', mp', ep',
		  cs @ cs'
		  @ (wf_cons ctx t')
		  @ (pscstr_wf ctx mp')
		  @ (pscstr_wf ctx ep')
		  @ (pscstr_eq ctx startprios sp)
		  @ (pscstr_sup ctx p midprios)
		  @ (pscstr_sup ctx p mp')
		 )
	     end
	  | _ => raise (TyError "not a cmd")
	)
      | Spawn (p, _, m) =>
	(case basety (cons ctx p) of
	     (TPrio psint, cs) =>
	     let val (t, mp, ep, cs') = conscmd psint ctx m
		 val pp' = new_psevar ()
	     in
		 (TThread (t, pp'),
		  sp,
		  sp,
		  cs @ cs'
		  @ (pscstr_gen ctx psint pp' mp)
		 )
	     end
	   | (t, _) => (Layout.print (ILPrint.ttol t, print);
			raise (TyError "not a prio"))
	)
	    
      | Sync e =>
	(case basety (cons ctx e) of
	     (TThread (t, p'), cs) =>
	     (t, sp, sp, cs @ (pscstr_cons ctx sp p'))
	   | _ => raise (TyError "not a thread")
	)
	     
      | Poll e =>
	(case basety (cons ctx e) of
	     (TThread (t, p'), cs) =>
	     (t, sp, sp, cs)
	   | _ => raise (TyError "not a thread")
	)
      | Cancel e =>
	(case basety (cons ctx e) of
	     (TThread (t, p'), cs) =>
	     (t, sp, sp, cs)
	   | _ => raise (TyError "not a thread")
	)
      | Ret e =>
	let val (t, cs) = cons ctx e
	in
	    (t, sp, sp, cs)
	end

      | Change p =>
	(case basety (cons ctx p) of
	     (TPrio ep', cs) =>
	     (TRec [], ep', ep', cs)
	   | _ => raise (TyError "not a priority")
	)
    end

and consdec ctx d =
    case d of
	Do e =>
	let val (_, cs) = cons ctx e in
	    (ctx, [], cs)
	end
      | Val (Poly ({tys}, (x, t, e))) =>
	let val (t', cs) = cons ctx e in
	    (C.bindv ctx (V.show x) (mkpoly t') x,
	     [(x, e)],
	     cs @ (print "subtype val\n"; subtype ctx t' t)
	    )
	end
      | Tagtype a => (ctx, [], [])
      | Newtag (c, t, a) => (ctx, [], [])
      | Priority p =>
	let val _ = print ("IL prio dec " ^ (V.show p) ^"\n")
	    val ps = PSSet (PrioSet.singleton (PVar p))
	    val ctx' = C.bindv ctx (V.show p) (mkpoly (TPrio ps)) p
	in
	    (ctx', [], [])
	end

fun consprog (decs, prios, cons, fairness, maincmd) =
    let val (ctx, cs) =
	List.foldl
	    (fn (d, (ctx, cs)) =>
		 let val (ctx', _, cs') = consdec ctx d in
		     (ctx', cs @ cs')
		 end
	    )
	    (C.empty, [])
	    decs
	val (_, _, _, cs') = conscmd (PSSet (PrioSet.singleton (PConst "bot")))
				     ctx maincmd
    in
	cs @ cs'
    end
	
end
