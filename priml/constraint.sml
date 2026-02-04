structure Constraint =
struct

open IL
structure C = Context
structure V = Variable

open PSetCstrs
     
exception PriorityErr of string
exception TyError of string

fun mkpoly t = Poly ({tys = []}, t)

val new_psevar = PSetCstrs.new_prioset

fun basety (t, cs) =
    case t of
	(Evar (ref (Bound t))) => basety (t, cs)
      | _ => (t, cs)

fun basety_plain t =
    case t of
	(Evar (ref (Bound t))) => basety_plain t
      | _ => t

fun supertypex ctx (loc: Pos.pos) (msg: string) t1 t2 =
    let val ctxlen = List.length (Context.vars ctx)
	val _ =
	    verb (fn () => Layout.print (Layout.listex
				  ("supertype " ^ (Int.toString ctxlen) ^ " (") ")\n" ","
				  (map ILPrint.ttol [t1, t2]),
			      print))
    in
        (case (t1, t2) of
             (TVar v1, TVar v2) => []
           | (TTag (t1, v1), TTag (t2, v2)) => 
             supertypex ctx loc msg t1 t2
           | (TVec t1, TVec t2) => supertypex ctx loc msg t1 t2
           | (TCont t1, TCont t2) => supertypex ctx loc msg t1 t2
           | (TRec lcl1, TRec lcl2) =>
             let
                 val l = ListUtil.sort 
                             (ListUtil.byfirst String.compare) lcl1
                 val r = ListUtil.sort 
                             (ListUtil.byfirst String.compare) lcl2
		 val cs = ListPair.map
			      (fn ((_, t1), (_, t2)) =>
				  supertypex ctx loc msg t1 t2)
			      (l, r)
             in
		 List.concat cs
	     end
           | (Arrow (_, dom1, cod1), Arrow (_, dom2, cod2)) => 
             let
		 val ctx' =
		     List.foldl
			 (fn ((v, t), ctx) =>
			     C.bindv ctx (V.basename v)
				     (Poly ({tys = []}, t)) v
			 )
			 ctx
			 dom2
		 val domcs = ListPair.map
			      (fn ((_, a), (_, b)) =>
				  supertypex ctx loc msg b a
					     (* FIX: domain is contravariant *)
			      )
                              (dom1, dom2)

		 val codcs = supertypex ctx' loc msg cod1 cod2
	     in
		 List.concat (codcs::domcs)
             end
           | (TRef c1, TRef c2) => supertypex ctx loc msg c1 c2
           | (Mu (_, m1), Mu (_, m2)) => 
             let val cs = ListPair.map (fn ((_, t1), (_, t2)) =>
					   supertypex ctx loc msg t1 t2)
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
                                            supertypex ctx loc msg tt1 tt2
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
				 let val ctx' =
					 List.foldl
					     (fn ((v, t), ctx) =>
						 C.bindv ctx (V.basename v)
							 (Poly ({tys = []}, t)) v
					     )
					     ctx
					     dom2
				 in
				     List.concat
				     (
				      (supertypex ctx' loc msg cod1 cod2)::
                                 (ListPair.map
				     (fn ((_, a), (_, b)) =>
					 supertypex ctx loc msg b a
						    (* FIX: domain is contravariant *)
				     )
				     (dom1, dom2)
				     ))
				 end
			     )
			     (al1, al2)
		 in
		     List.concat cs
		 end
           | (TCmd (t1, (pi1, pp1, pf1)), TCmd (t2, (pi2, pp2, pf2))) =>
               (pscstr_sup ctx pi2 pi1 loc msg) (* FIX: start refinement contravariant *)
               @ (pscstr_sup ctx pp1 pp2 loc msg)
               @ (pscstr_sup ctx pf1 pf2 loc msg)
	       @ (supertypex ctx loc msg t1 t2)
           | (TThread (t1, ps1), TThread (t2, ps2)) =>
	     (pscstr_sup ctx ps1 ps2 loc msg) @ (supertypex ctx loc msg t1 t2)
           | (TPrio ps1, TPrio ps2) => pscstr_sup ctx ps1 ps2 loc msg
	   | (TMutex ps1, TMutex ps2) => pscstr_sup ctx ps1 ps2 loc msg
	   | (Evar (ref (Bound t1)), Evar (ref (Bound t2))) =>
	     supertypex ctx loc msg t1 t2
	   | (Evar (ref (Bound t1)), t2) => supertypex ctx loc msg t1 t2
	   | (t1, Evar (ref (Bound t2))) => supertypex ctx loc msg t1 t2
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

fun subtype ctx loc msg t1 t2 =
    (verbprint "subtype\n";
    (supertypex ctx loc msg t2 t1)
    handle TyError s => (print s; raise (TyError s))
    )	
fun wf_cons ctx loc msg t =
    let val _ =
	    verbprint ("wf_cons " ^ (Layout.tostring (ILPrint.ttol t)) ^ "\n")
    in
    case t of
	TVar _ => []
      | TRec fields =>
	List.concat (List.map (fn (_, t) => wf_cons ctx loc msg t) fields)
      | Arrow (_, dom, cod) =>
	let val ctx' =
		List.foldl
		    (fn ((arg, ty), ctx) =>
			C.bindv ctx (V.basename arg) (mkpoly ty) arg
		    )
		    ctx
		    dom
	    val dom_cons = List.map (fn (_, t) => wf_cons ctx loc msg t) dom
	in
	    (wf_cons ctx' loc msg cod) @ (List.concat dom_cons)
	end
      | Sum arms =>
	List.concat (List.map (fn (_, ai) =>
				  case ai of NonCarrier => []
					   | Carrier {carried, ...} =>
					     wf_cons ctx loc msg carried
			      )
			      arms)
      | Mu (i, typs) =>
	List.concat (List.map (fn (_, t) => wf_cons ctx loc msg t) typs)
      | Evar (ref (Free _)) => []
      | Evar (ref (Bound t)) => wf_cons ctx loc msg t
      | TVec t => wf_cons ctx loc msg t
      | TCont t => wf_cons ctx loc msg t
      | TRef t => wf_cons ctx loc msg t
      | TTag (t, _) => wf_cons ctx loc msg t
      | Arrows fns =>
	List.concat
	    (List.map
		 (fn (_, dom, cod) =>
		     let val ctx' =
			     List.foldl
				 (fn ((arg, ty), ctx) =>
				     C.bindv ctx (V.basename arg) (mkpoly ty) arg
				 )
				 ctx
				 dom
			 val dom_cons = List.map (fn (_, t) => wf_cons ctx loc msg t) dom
		     in
			 (wf_cons ctx' loc msg cod) @ (List.concat dom_cons)
		     end
		 )
		 fns
	    )
      | TCmd (t, (p1, p2, p3)) =>
	(verbprint "cmd\n";
	 (pscstr_wf ctx p1 loc msg)
	@ (pscstr_wf ctx p2 loc msg)
	@ (pscstr_wf ctx p3 loc msg)
	@ (wf_cons ctx loc msg t))
      | TThread (t, p) => (pscstr_wf ctx p loc msg) @ (wf_cons ctx loc msg t)
      | TPrio p => (pscstr_wf ctx p loc msg)
      | TMutex p => pscstr_wf ctx p loc msg
    end


fun fresh t =
    let val _ =
	    verbprint ("fresh " ^ (Layout.tostring (ILPrint.ttol t)) ^ "\n")
    in
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
      | TPrio (_, (RConcrete _)) => t
      | TPrio (substs, RVar _) => TPrio (substs, PSetCstrs.new_rvar ())
      | TMutex _ => TMutex (new_psevar ())
    end		 


fun consval ctx loc v =
    let val _ =
	    verb (fn () => Layout.print (Layout.mayAlign [Layout.str "consval ",
					       ILPrint.vtol v,
					       Layout.str "\n"], print)
		 )
    in
    case v of
	Polyvar {tys, var} =>
	let val (t, cs) =
	(case C.var_fail ctx (V.basename var) of
	     (Poly (_, TPrio ps), _, _) =>
	     (TPrio (singleton_prioset (PVar var)),
	      [])
	   | (Poly ({tys=tyvars}, t), _, _) =>
	     let val ftps = List.map fresh tys
		 val subst = Subst.fromlist
				 (ListPair.zip (tyvars, ftps))
	     in
		 (Subst.tsubst subst t,
		  List.concat (List.map (wf_cons ctx loc "type parameter") ftps))
	     end
	)
	in
	    verb (fn () =>
	    Layout.print (Layout.mayAlign [Layout.str "type of ",
					   Layout.str (V.show var),
					   Layout.str ": ",
					   ILPrint.ttol t],
			  print));
	    (t, cs)
	end
      | Polyuvar {tys, var} =>
	let val (t, cs) =
	(case C.var_fail ctx (V.basename var) of
	     (Poly (_, TPrio ps), _, _) =>
	     (TPrio (singleton_prioset (PVar var)),
	      [])
	   | (Poly ({tys=tyvars}, t), _, _) =>
	     let val ftps = List.map fresh tys
		 val subst = Subst.fromlist
				 (ListPair.zip (tyvars, ftps))
	     in
		 (Subst.tsubst subst t,
		  List.concat (List.map (wf_cons ctx loc "type parameter") ftps))
	     end
	)
	in
	    verb (fn () =>
	    Layout.print (Layout.mayAlign [Layout.str "type of ",
					   Layout.str (V.show var),
					   Layout.str ": ",
					   ILPrint.ttol t],
			  print));
	    (t, cs)
	end
      | MLVal _ => raise (PriorityErr "what's an mlval?")
      | Int _ => (Initial.ilint, [])
      | String _ => (Initial.ilstring, [])
      | Prio p => (TPrio (singleton_prioset p), [])
      | VRecord fields =>
	let val (ts, ccs) =
	    List.foldl (fn ((l, v), (ts, ccs)) =>
			   let val (t, cs) = consval ctx loc v in
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
		SOME v => #2 (consval ctx loc v)
	      | NONE => []
	in
	    (t, cs)
	end
      | Fns fs =>
	let val orig_ctx = ctx
	    val (cons_wf, ctx) =
	    List.foldl
		(fn (f, (cons_wf, ctx)) =>
		    let val at =
			    Arrow (false,
				   ListPair.zip (#arg f, #dom f),
				   #cod f)
			val t = mkpoly at
		    in
			((wf_cons orig_ctx loc "function type" at) @ cons_wf,
			 C.bindv ctx (V.basename (#name f)) t (#name f))
		    end
		)
		([], ctx)
		fs
	    fun consf f =
		let val ctx' =
			ListPair.foldl
			(fn (arg, ty, ctx) =>
			    C.bindv ctx (V.basename arg) (mkpoly ty) arg
			)
			ctx
			(#arg f, #dom f)
		in
		    cons ctx' loc (#body f)
		end
	    val tscs = List.map consf fs
	    val (ts, cs) = ListPair.unzip tscs
	in
	    
	(Arrows (ListPair.map (fn (f, t) => (false, ListPair.zip (#arg f, #dom f), t)) (fs, ts)),
	 cons_wf @ (List.concat cs)
	)
	end
      | FSel (n, fs) =>
	(case consval ctx loc fs of
	     (Arrows ts, cs) => (Arrow (List.nth (ts, n)), cs)
	   | _ => raise (PriorityErr "FSel value is not Fns")
	)
      | PCmd (p, t, cmd) =>
	let val (t, midprios, endprios, cs) = conscmd p ctx loc cmd in
	    (TCmd (t, (p, midprios, endprios)), cs)
	end
end
	    
and cons ctx loc e : typ * (psconstraint list) =
    let val _ =
	    verb (fn () =>
		     Layout.print (Layout.mayAlign [Layout.str "cons ",
					       ILPrint.etol e,
					       Layout.str "\n"], print))
    in
    case e of
	Value v => consval ctx loc v
      | Loc (loc, e) => cons ctx loc e
      | App (efun, eargs) =>
	let val (funty, cs) = cons ctx loc efun
	    val (argtys, css) = ListPair.unzip (List.map (cons ctx loc) eargs)
	in
	    case basety_plain funty of
		Arrow (_, dom, cod) =>
		let val subcs = ListPair.map
				    (fn (argty, (_, party)) =>
					subtype ctx loc "function argument" argty party)
				    (argtys, dom)
		    val substs =
			ListPair.map
			    (fn ((x, _), (arg, argt)) =>
				case (arg, argt) of
				    (Value (Polyvar {var, ...}), _) =>
				    (* Just sub in the var *)
				    (x, SubstVar var)
				  | (_, TPrio s) => 
				    (* Going to lose some precision here,
				     * but at least sub in the refinement *)
				    (x, SubstSet s)
				  | _ =>
				    (* The arg isn't a priority, so it's not
				     * dependent anyway. *)
				    (x, DontSubst))
			    (dom, ListPair.zip (eargs, argtys))
		    val t =
			Subst.subst_var_or_t_in_t (Subst.fromlist substs) cod
		in
		    (t,
		     List.concat (cs::(css @ subcs)))
		end
	      | _ => raise (TyError "not an arrow")
	end
      | Record fields =>
	let val (ts, ccs) =
		List.foldl (fn ((l, v), (ts, ccs)) =>
			       let val (t, cs) = cons ctx loc v in
				   ((l, t)::ts, cs @ ccs)
			       end)
			   ([], [])
			   fields
	in
	    (TRec (List.rev ts), ccs)
	end
      | Proj (label, t, e) =>
	let val field_t =
		case basety_plain t of
		    TRec fields =>
		    (case List.filter (fn (l, _) => l = label) fields of
			 (_, t)::_ => t
		       | _ => raise (TyError "field not found")
		    )
		  | _ => raise (TyError "not a record type")
	    val (et, cs) = cons ctx loc e
	in
	    (field_t, (subtype ctx loc "tuple type" et t) @ cs)
	end
      | Raise (t, e) =>
	let val (_, cs) = cons ctx loc e in
	    (t, cs)
	end
	
      (* var bound to exn value within handler*)
      | Handle (ebody, t, evar, handler) =>
	let val (_, cs1) = cons ctx loc ebody
	    val ctx' = C.bindv ctx (V.basename evar) (mkpoly Initial.ilexn) evar
	    val (_, cs2) = cons ctx' loc handler
	in
	    (t, cs1 @ cs2)
	end

      | Seq (e1, e2) =>
	let val (_, cons1) = cons ctx loc e1
	    val (t2, cons2) = cons ctx loc e2
	in
	    (t2, cons1 @ cons2)
	end

      | Let (d, ebody, t) =>
	(*
	let val F = fresh t
	    val (ctx', subs, cs) = consdec ctx d
	    val (F2, cs') = cons ctx' ebody
	    val _ = print "subtype let\n"
	    val _ = print ((Int.toString (List.length subs)) ^ " subs")
	    val subcs = subtype ctx' F2 F
	    val t' = Subst.subst_var_or_t_in_t (Subst.fromlist subs) F
	in
	    (t',
	     cs @ cs' @ subcs @ (wf_cons ctx t'))
	end
	*)
	(* This differs from the Liquid Types paper, but seems OK *)
	(* Maybe---with the fix? *)
	let val (ctx', subs, cs) = consdec ctx loc d
	    val (F, cs') = cons ctx' loc ebody
	    val _ = verbprint "subtype let\n"
	    val _ = verb (fn () => print ((Int.toString (List.length subs)) ^ " subs"))
	    val t' = Subst.subst_var_or_t_in_t (Subst.fromlist subs) F
	in
	    (t', cs @ cs')
	end
	
      | Unroll e =>
	(case basety (cons ctx loc e) of
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
	let val (_, cs) = cons ctx loc e in
	    (t, cs)
	end

      (* tag v with t *)
(*
      | Tag (e, Value (Polyvar {var = tag, ...})) =>
	(print ("Looking up " ^ (V.basename tag) ^ "\n");
	 case C.con ctx (V.basename tag) of
	     (_, Typ (Arrow (_, _, t)), _) => (t, [])
	   | _ => raise (TyError "Invalid tag")
	)
*)
      | Tag _ => (TVar (V.namedvar "exn"), []) (* XXX *)

      | Untag _ => (TRec [], []) (* XXX *)

      (* apply a primitive to some expressions and types *)
      | Primapp (po, eargs, argtys) =>
	let
            val { worlds, tys, dom, cod } = Podata.potype po
	    val (_, cs) = ListPair.unzip
			      (List.map (cons ctx loc) eargs)
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
	    val (_, cs) = cons ctx loc ecase
	    val _ = verbprint "Done checking ecase\n"
	    fun getarm arms l =
		case arms of
		    [] => raise (TyError "sum arm not found")
		  | (l', arm)::t => if l = l' then arm else getarm t l
	    val getarm = getarm constrs
	    val _ = verbprint "ecase:\n"
	    val _ = verb (fn () => Layout.print
				       (ILPrint.etol ecase, print))
	    
	    val (tys, css) =
		ListPair.unzip
		    (List.map
			 (fn (l, e) =>
			     let val ctx' =
				     case getarm l of
					 NonCarrier =>
					 (verbprint "Not a carrier"; ctx)
				       | Carrier {carried, ...} =>
					 (verbprint ("Adding " ^ (V.basename branchvar));
					 C.bindv ctx
					       (V.basename branchvar)
					       (mkpoly carried)
					       branchvar)
			     in
				 cons ctx' loc e
			     end)
			 branches)
	    val (dty, dcs) = cons ctx loc def
	    val _ = verbprint "Subtyping for branches"
	    val subtycs =
		List.concat
		    (List.map (supertypex ctx loc "branch type" F) (dty::tys))
	in
	    (F, cs @ dcs @ subtycs @ (wf_cons ctx loc "return type" F) @ (List.concat css))
	end

      (* simpler; no inner val needs to be defined. can't be exhaustive. *)
      | Intcase (ecase, branches, def, rett) =>
	let val F = fresh rett
	    val (_, cs) = cons ctx loc ecase
	    val (tys, css) =
		ListPair.unzip
		    (List.map (fn (_, e) => cons ctx loc e) branches)
	    val (dty, dcs) = cons ctx loc def
	    val subtycs =
		List.concat
		    (List.map (supertypex ctx loc "branch type" F) (dty::tys))
	in
	    (F, cs @ dcs @ subtycs @ (wf_cons ctx loc "return type" F) @ (List.concat css))
	end

      | Priocomp (conds, etrue, efalse, rett) => 
	let val (truectx, falsectx) =
		(* If this is a priority comparison, we want to add constraints
		 * to the context *)
		case conds of
		    [(p1, p2)] =>
		    (verbprint "binding one less-equal constraint\n";
		    (Context.bindplecons ctx (p1, p2),
		     (* Technically this just adds p2 <= p1 when we know p2 < p1
		      * but that just loses a little precision *)
		     Context.bindplecons ctx (p2, p1))
		    )
		  | conds =>
		    (* In the true case, add all of the conditions.
		     * In the false case, can't add anything because we
		     * don't know which conditions aren't true *)
		    (List.foldl
			 (fn ((p1, p2), ctx) =>
			     Context.bindplecons ctx (p1, p2))
			 ctx
			 conds,
		     ctx)
	    val F = fresh rett
	    val (ty1, cs1) = cons truectx loc etrue
	    val (ty2, cs2) = cons falsectx loc efalse
	    val cssup = (supertypex ctx loc "branch type" F ty1)
			@ (supertypex ctx loc "branch type" F ty2)
	in
	    (F, cs1 @ cs2 @ cssup @ (wf_cons ctx loc "return type" F))
	end

      | Inject (t, label, eopt) =>
	(case eopt of
	     NONE => (t, [])
	   | SOME e =>
	     let val (_, cs) = cons ctx loc e
	     in
		 (t, cs)
	     end
	)
	
      | Cmd (p, cmd) =>
	let val (t, midprios, endprios, cs) = conscmd p ctx loc cmd
	in
	    (TCmd (t, (p, midprios, endprios)),
	     cs)
	end
      | NewMutex p =>
	(case basety (cons ctx loc p) of
	    (TPrio psint, cs) =>
	    (TMutex psint, cs)
	  | (t, _) => (Layout.print (ILPrint.ttol t, print);
		       Layout.print (Context.ctol ctx, print);
		       raise (TyError "not a prio"))
	)
      | Constrain (e, tc) =>
	let val (t, cs) = cons ctx loc e
	    val _ = verbprint "constrain\n"
	in
	    (tc, (subtype ctx loc "type annotation" t tc) @ cs)
	end
	    
    end
	
and conscmd sp ctx loc cmd =
    let val _ = verb (fn () => Layout.print (Layout.mayAlign [Layout.str "cons ",
					       ILPrint.ctol cmd,
					       Layout.str "\n"], print))
    in
    case cmd of
	CLoc (loc, cmd) => conscmd sp ctx loc cmd	    
      | Bind (x, e, m) =>
	(case basety (cons ctx loc e) of
	     (TCmd (t, (startprios, midprios, endprios)), cs) =>
	     let val ctx' = C.bindv ctx (V.basename x) (mkpoly t) x
		 val p = new_psevar ()
		 val (t', mp', ep', cs') = conscmd endprios ctx' loc m
		 val subst =
		     case t of
			 TPrio s =>
			 (* Going to lose some precision here,
			  * but at least sub in the refinement *)
			 (x, SubstSet s)
		       | _ =>
			 (* The arg isn't a priority, so it's not
			  * dependent anyway. *)
			 (x, DontSubst)
		 val t' = Subst.subst_var_or_t_in_t (Subst.fromlist [subst]) t'
	     in
		 (t', p, ep',
		  cs @ cs'
		  @ (wf_cons ctx loc "cmd return type" t)
		  @ (wf_cons ctx loc "return type" t')
		  @ (pscstr_wf ctx p loc "comprehensive priority of whole cmd")
		  @ (pscstr_wf ctx startprios loc "start priority of cmd")
		  @ (pscstr_wf ctx midprios loc "comprehensive priority of cmd")
		  @ (pscstr_wf ctx endprios loc "end priority of cmd")
		  @ (pscstr_wf ctx mp' loc "comprehensive priority of rest of cmd")
		  @ (pscstr_wf ctx ep' loc "end priority of whole cmd")
		  (* @ (pscstr_eq ctx startprios sp) *)
		  @ (pscstr_sup ctx startprios sp loc "starting priority")
		  @ (pscstr_sup ctx p midprios loc "comprehensive priority of cmd subset of whole")
		  @ (pscstr_sup ctx p mp' loc "comprehensive priority of rest of cmd subset of whole")
		 )
	     end
	  | _ => raise (TyError "not a cmd")
	)
      | Spawn (p, _, m) =>
	(case basety (cons ctx loc p) of
	     (TPrio psint, cs) =>
	     let (* Don't prematurely specialize the start priority, as we
		  * may add to it *)
		 val spawnprio = new_psevar ()
		 val (t, mp, ep, cs') = conscmd spawnprio ctx loc m
		 val pp' = new_psevar ()
	     in
		 (TThread (t, pp'),
		  sp,
		  sp,
		  cs @ cs'
		  @ (pscstr_sup ctx spawnprio psint loc "starting priority of thread")
		  @ (pscstr_gen ctx psint pp' mp loc "comprehensive priority of thread")
		 )
	     end
	   | (t, _) => (Layout.print (ILPrint.ttol t, print);
			Layout.print (Context.ctol ctx, print);
			raise (TyError "not a prio"))
	)
	    
      | Sync e =>
	(case basety (cons ctx loc e) of
	     (TThread (t, p'), cs) =>
	     (t, sp, sp, cs @ (pscstr_cons ctx sp p' loc "sync priority"))
	   | _ => raise (TyError "not a thread")
	)
	     
      | Poll e =>
	(case basety (cons ctx loc e) of
	     (TThread (t, p'), cs) =>
	     (t, sp, sp, cs)
	   | _ => raise (TyError "not a thread")
	)
      | Cancel e =>
	(case basety (cons ctx loc e) of
	     (TThread (t, p'), cs) =>
	     (t, sp, sp, cs)
	   | _ => raise (TyError "not a thread")
	)
      | Ret e =>
	let val (t, cs) = cons ctx loc e
	in
	    (t, sp, sp, cs)
	end

      | Change p =>
	(case basety (cons ctx loc p) of
	     (TPrio ep', cs) =>
	     (TRec [], ep', ep', cs)
	   | _ => raise (TyError "not a priority")
	)

      | WithMutex (mut, c) =>
	(* Priority protection protocol: the critical section starts at the
	 * priority ceiling and must stay at the priority ceiling *)
	(case basety (cons ctx loc mut) of
	     (TMutex pc, cs) =>
	     let val (t, mp, ep, cs') = conscmd pc ctx loc c
		 val allp = new_psevar ()
	     in
		 (t, allp, sp,
		  cs @ cs'
		  @ (pscstr_cons ctx sp pc loc "priority ceiling violated")
		  @ (pscstr_sup ctx allp sp loc "critical section comprehensive priority")
		  @ (pscstr_sup ctx allp mp loc "critical section comprehensive priority")
		  @ (pscstr_eq ctx mp pc loc "critical section comprehensive priority")
		 )
	     end
	   | _ => raise (TyError "not a priority")
	)
    end

and consdec ctx loc d =
    let val _ = verb (fn () => Layout.print (C.ctol ctx, print))
    in
    case d of
        DLoc (loc, d) => consdec ctx loc d
      | Do e =>
	let val (_, cs) = cons ctx loc e in
	    (ctx, [], cs)
	end
      | Val (Poly ({tys}, (x, t, e))) =>
	let val (t', cs) = cons ctx loc e in
	    (C.bindv ctx (V.basename x) (Poly ({tys = tys}, t')) x,
	     (verb (fn () => (print "collecting subs for ";
	      print (V.basename x);
	      print "\n";
	      print "type: ";
	      print (Layout.tostring (ILPrint.ttol t));
	      print "\n"));
	      case (e, t') of
		  (Value (Polyvar {var, ...}), _) =>
		  (verbprint "substvar\n";
		 (* Just sub in the var *)
		 [(x, SubstVar var)])
	       | (_, TPrio s) =>
		 (verbprint "substset\n";
		 (* Going to lose some precision here,
		  * but at least sub in the refinement *)
		 [(x, SubstSet s)])
	       | _ => (verbprint "dontsubst\n"; []))
	     ,
	     cs @ (verbprint "subtype val\n"; subtype ctx loc "type annotation" t' t before verbprint "done\n")
	    )
	end
      | Tagtype a => (ctx, [], [])
      | Newtag (c, t, a) => (ctx, [], [])

      | ExternVal (Poly ({tys}, (v, t))) =>
	(C.bindv ctx (V.basename v) (Poly ({tys = tys}, t)) v,
	 [],
	 []
	)
      | ExternType v =>
	(C.bindc ctx (V.basename v) (Typ (TVar v)) 0 Regular,
	 [],
	 [])
			    
      | Priority p =>
	let val vv = Variable.namedvar p
	      val p' = PVar vv
	      val ps = singleton_prioset (PConst p)
              val tt = TPrio (ps (*PSSet (PrioSet.singleton p')*))
	      val ctx = C.bindex ctx (SOME p) (Poly ({tys = nil}, tt)) vv Normal
              val ctx = C.bindplab ctx p
	in
	    (ctx, [], [])
	end
      | Order (p1, p2) =>
	let val (p1, p2) = (C.prio ctx p1, C.prio ctx p2)
	in
	    (C.bindpcons ctx (p1, p2),
	     [],
	     []
	    )
	end
    end

fun consprog (decs, prios, cons, fairness, maincmd) =
    let val (ctx, cs) =
	List.foldl
	    (fn (d, (ctx, cs)) =>
		 let val (ctx', _, cs') = consdec ctx Pos.initpos d in
		     (ctx', cs @ cs')
		 end
	    )
	    (Initial.initial, [])
	    decs
	val (_, _, _, cs') = conscmd (singleton_prioset (PConst "bot"))
				     ctx Pos.initpos maincmd
    in
	cs @ cs'
    end
	
end
