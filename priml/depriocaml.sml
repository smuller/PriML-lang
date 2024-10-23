structure DePrio =
struct

open EL

exception unimplemented
exception CyclicPriorities

val poolvar = "__pool"

fun anonfn (pats: pat list) (e as (e_, loc): exp) : exp_ =
    Let ((Fun {inline = false,
                funs = [([], "anonfn", [(pats, NONE, e)])]}, loc),
         (Var (Id "anonfn"), loc))

fun deprioe ((e, loc): exp) : exp =
    (case e of
        Constant _ => e
      | Var _ => e
      | Float _ => e
      | App (e1, e2, i) => App (deprioe e1, deprioe e2, i)
      | Let (d, e) => Let (depriod d, deprioe e)
      | Record ses =>
        Record (List.map (fn (s, e) => (s, deprioe e)) ses)
      | Vector es => Vector (List.map deprioe es)
      | Proj (s, t, e) => Proj (s, depriot t, deprioe e)
      | Andalso (e1, e2) => Andalso (deprioe e1, deprioe e2)
      | Orelse (e1, e2) => Orelse (deprioe e1, deprioe e2)
      | Andthen (e1, e2) => Andthen (deprioe e1, deprioe e2)
      | Otherwise (e1, e2) => Otherwise (deprioe e1, deprioe e2)
      | If (e1, e2, e3) => If (deprioe e1, deprioe e2, deprioe e3)
      | Primapp (s, ts, es) =>
        Primapp (s, List.map depriot ts, List.map deprioe es)
      | Seq (e1, e2) => Seq (deprioe e1, deprioe e2)
      | Constrain (e, t) => Constrain (deprioe e, depriot t)
      | Raise e => Raise (deprioe e)
      | Case (es, pes, opt) =>
        Case (List.map deprioe es,
              List.map (fn (ps, e) => (ps, deprioe e)) pes,
              opt)
      | CompileWarn _ => e
      | ECmd c =>
        (* Wrap the expression in a thunk to preserve encapsulation *)
        anonfn [PWild] (deprioc (c, loc))
      | NewMutex e =>
	App ((App ((Var (Id "Domainslib.Task.Mutex.create"), loc),
		   (LabeledArg ("ceil", deprioe e), loc),
		   false),
	      loc),
	     (Record [], loc),
	     false)
	
      (* | PFn (ppats, pats, e) =>
        let val ee = deprioe e
        in
            anonfn pats ee
        end (* FIX: delete this *) *)
      (* | PApply (e, p) => App (deprioe e, depriop loc p, false) (* FIX: delete this *) *)
      | Handle (e, pes) =>
        Handle (deprioe e, List.map (fn (p, e) => (p, deprioe e)) pes),
     loc)

    (*
and depriop loc p = (Var (Id p), loc)
*)
and deprioc ((c, loc) : cmd) : exp =
    let fun apptopool f =
	    (App ((Var (Id f), loc), (Var (Id poolvar), loc), false), loc)
    in
    case c of
	IBind (ses, e) =>
	List.foldr
        (fn ((s, e), ee) => (Let ((Val ([], PVar s, (App (deprioe e, (Record [], #2 e), false), #2 e)), #2 e), ee), #2 e))
        (App (deprioe e, (Record [], #2 e), false), #2 e)
        ses
      | Spawn (p, c) =>
        (App((App (apptopool "Domainslib.Task.async",
		   (LabeledArg ("prio", deprioe p), loc), false), loc),
                   (anonfn [PWild] (deprioc c), loc), false), loc)
             
      | Sync e => (App (apptopool "Domainslib.Task.await", deprioe e, false), loc)
      | Poll e => (App (apptopool "Domainslib.Task.poll", deprioe e, false), loc)
      | Cancel e => (App (apptopool "Domainslib.Task.cancel", deprioe e, false), loc)
      | IRet e => deprioe e
      (* TODO: Threshold deprioc rule for Change. Should update to use the right 
      * function in Thread module for updating priority *)
      | Change p =>
        (App (apptopool "Domainslib.Task.change",
	       (LabeledArg ("prio", deprioe p), loc)
	    , false), loc)
      | WithMutex (e, c) =>
	List.foldr
	    (fn ((v, e), e') => (Let ((Val ([], PVar v, e), loc), e'), loc))
	    (Var (Id "__ret"), loc)
	    [("_", (App (apptopool "Domainslib.Task.Mutex.lock", deprioe e, false), loc)),
	     ("__ret", deprioc c), (*(App (deprioc c, (Record [], #2 c), false), loc)),*)
	     ("_", (App (apptopool "Domainslib.Task.Mutex.unlock", deprioe e, false), loc))]

    end

and depriot (t: typ) =
    case t of
        TVar _ => t
      | TApp (ts, s) => TApp (List.map depriot ts, s)
      | TRec sts => TRec (List.map (fn (s, t) => (s, depriot t)) sts)
      | TArrow (t1, t2) => TArrow (depriot t1, depriot t2)
      | TNum _ => t
      | TCmd (t, p) => TArrow (TRec [], depriot t)
      | TThread (t, p) => TApp ([depriot t], "Domainslib.Task.t")
      | TPrio _ => TVar "Domainslib.Priority.t"
      | TMutex _ => TVar "Domainslib.Task.Mutex.t"
      
      (* | TForall (_, t) => depriot t (* FIX: delete this *) *)

and onefun (ss, s, pats) =
    (ss, s, List.map (fn (ps, SOME t, e) => (ps, SOME (depriot t), deprioe e)
                     | (ps, NONE, e) => (ps, NONE, deprioe e))
                     pats)

and onecon (s, sts) =
    (s, List.map (fn (s, SOME t) => (s, SOME (depriot t))
                 | (s, NONE) => (s, NONE))
                 sts)

and depriopp (pp: ppat) : pat =
    case pp of
        PPVar s => PVar s
      | PPConstrain (s, _) => PVar s

and depriod ((d, l) : dec) : dec =
    (case d of
        Val (ss, p, e) => Val (ss, p, deprioe e)
      | SigVal (s, t) => SigVal (s, depriot t)
      | SigType (ss, s) => SigType (ss, s)
      | Do e => Do (deprioe e)
      | Type (ss, s, t) => Type (ss, s, depriot t)
      | Fun {inline, funs} => Fun {inline = inline, funs = List.map onefun funs}
      (* | WFun (s, ppats, pats, tyo, e) =>
        let val tyo = case tyo of SOME t => SOME (depriot t) | NONE => NONE
            val pvars = List.map depriopp ppats
        in
            Fun {inline = false,
                 funs = [([], s, [(pvars @ pats, tyo, deprioe e)])]}
        end (* FIX: delete this *) *)
      | Datatype (ss, cs) => Datatype (ss, List.map onecon cs)
      | Tagtype _ => d
      | Newtag (s1, SOME t, s2) => Newtag (s1, SOME (depriot t), s2)
      | Newtag (s1, NONE, s2) => Newtag (s1, NONE, s2)
      | Exception (s, SOME t) => Exception (s, SOME (depriot t))
      | Exception (s, NONE) => Exception (s, NONE)
      | ExternVal _ => Val ([], PWild, (Record [], Pos.initpos))
      | ExternType _ => Val ([], PWild, (Record [], Pos.initpos))
      | Structure (id, decs) => Structure (id, List.map depriod decs)
      | Signature (id, decs) => Signature (id, List.map depriod decs),
     l)

and deprioprog (Prog (tds, c)) : dec list =
    case tds of
        [] =>
	[(Fun {inline = false,
	       funs = [([], "__main", [([PWild], NONE, deprioc c)])]
	}, Pos.initpos)]
      | (Dec d)::tds' => (depriod d)::(deprioprog (Prog (tds', c)))
      | (Priority _)::tds' => deprioprog (Prog (tds', c))
      | (Order _)::tds' => deprioprog (Prog (tds', c))
      | (Fairness _)::tds' => deprioprog (Prog (tds', c))

fun priotocaml l (p: string) : dec =
    (Val ([], PVar p,
          (if p = "bot" then (Var (Id "Domainslib.Priority.bot"), l)
           else
               (App ((Var (Id "Domainslib.Priority.new_priority"), l), (Record [], l), false), l)
          )), l)

fun constocaml l (s1, s2) : dec =
    (Val ([], PWild, (App ((App ((Var (Id "Domainslib.Priority.new_lessthan"), l),
                                 (Var (Id s1), l),
                                 false), l),
                           (Var (Id s2), l),
                           false), l)),
     l)

fun fairtocaml l sns : dec list =
    let fun onefair ((s, n), caml) =
            (If ((App ((Var (Id "Domainslib.Priority.pe"), l),
                       (Record [("1", (Var (Id s), l)), ("2", (Var (Id "p"), l))], l),
                       false), l),
                 (Constant (CInt n), l),
                 caml),
             l)
        val catchall =
            (Constant (CInt 0w0), l)
    in
        [(Fun { inline = false,
                funs = [([], "cg__priodist",
                         [([PVar "p"], NONE, List.foldr onefair catchall sns)])]
              },
          l),
         (Val ([], PWild, (App ((Var (Id "Domainslib.Priority.installDist"), l),
                                (Var (Id "cg__priodist"), l),
                                false), l)),
         l)]
    end

fun decstolet decs =
    List.foldr (fn (d, e) => (Let (d, e), Pos.initpos))
	       (Record [], Pos.initpos)
	       decs

fun to_total prios cons =
    let val nbrs : string list StringMap.map =
	    List.foldl (fn ((p1, p2), nbrs) =>
			   case StringMap.find (nbrs, p1) of
			       SOME l => StringMap.insert (nbrs, p1, p2::l)
			    |  NONE => StringMap.insert (nbrs, p1, [p2])
		       )
		       (StringMap.insert (StringMap.empty,
					  "bot",
					  (List.filter
					       (fn p => String.compare
							    (p, "bot") <>
						   EQUAL)
					       prios))
		       )
		       cons
	val perm_visited = ref StringSet.empty
	val order = ref []
	fun toposort temp_visited p =
	    if StringSet.member (!perm_visited, p) then
		()
	    else if StringSet.member (temp_visited, p) then
		raise CyclicPriorities
	    else
		let val p_nbrs =
			case StringMap.find (nbrs, p) of
			    SOME l => l
			  | NONE => []
		in
		    List.app (toposort (StringSet.add (temp_visited, p)))
			     p_nbrs;
		    order := p::(!order);
		    perm_visited := StringSet.add (!perm_visited, p)
		end
    in
	toposort StringSet.empty "bot";
	List.app (toposort StringSet.empty) prios;
	!order
    end
	    

	
fun deprio p prios cons fs =
    let val l = Pos.initpos
    in
        (List.map (priotocaml l) (to_total prios cons)) @
	(*
        [(Val ([], PWild, (App ((Var (Id "Basic.initPriorities"), l),
                                (Record [], l),
                                false), l)), l)] @
	 *)


	(* XXX constraints temporarily disabled
        (List.map (constocaml l) cons) @
        (List.map (fn s => constocaml l ("bot", s))
                  (List.filter (fn s => s <> "bot") prios)) @
        (List.map (fn s => constocaml l (s, "(Domainslib.Priority.top ())")) prios) @

	 *)



	(*
        [(Val ([], PWild, (App ((Var (Id "Basic.finalizePriorities"), l),
                                (Record [], l),
                                false), l)), l)] @
        (case fs of [] => [] | _ => fairtocaml l fs) @
	 *)
        [(Val ([], PVar poolvar,
	       (App
		    (
		    (App ((Var (Id "Domainslib.Task.setup_pool"), l),
			  (LabeledArg ("num_domains", (Constant (CInt (IntConst.fromInt 8)), l)), l),
			  false), l),
                    (Record [], l),
                    false), 
		l)), l)] @
	(deprioprog p)  @
	    (*
	[(Fun {inline = false,
	       funs = [([], "__main", [([PWild], NONE, decstolet (deprioprog p))])]
	}, l)] @
	     *)
	[(Val ([], PWild,
	       (App ((Var (Id ("Domainslib.Task.run " ^ poolvar)), l), (Var (Id "__main"), l), false), l)), l)]
    end

end
