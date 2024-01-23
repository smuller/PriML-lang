
structure Unify :> UNIFY =
struct

    open IL
    open PSetCstrs 
        
    structure V = Variable.Map
        
    local 
        val last_tag = ref 0
    in
        fun new_ebind () =
            let in
                last_tag := !last_tag + 1;
                ref (Free (!last_tag))
            end
    end


    (* FIX: global constraints for priorities (instead of one for each priority) *)
    val global_cstrs = ref []


    val all_evars  = ref (nil : IL.typ IL.ebind ref list)
    (* FIX: delete this, no more priority evars *)
    val all_wevars = ref (nil : IL.prio IL.ebind ref list)
    val all_psevars = ref (nil : IL.prioset IL.ebind ref list)
    fun clear_evars () = (all_evars  := nil;
                          all_wevars := nil;
                          all_psevars := nil)

    fun get_psevars () = List.map (fn pseb => IL.PSEvar pseb) (!all_psevars)

    fun finalize_evars () =
      let in
        app (fn r =>
             case !r of
               IL.Bound _ => ()
             | IL.Free _ => r := IL.Bound (IL.TRec nil)) (!all_evars);
        app (fn r =>
             case !r of
               IL.Bound _ => ()
             | IL.Free _ => r := IL.Bound Initial.bot) (!all_wevars)
      end
    
    fun new_evar ()  = 
      let val e = new_ebind ()
      in
        all_evars := e :: !all_evars;
        IL.Evar e
      end
    (* FIX: delete this, no more priority evars *)
    fun new_pevar () =
      let val e = new_ebind ()
      in
        all_wevars := e :: !all_wevars;
        IL.PEvar e
      end
    fun new_psevar () = 
      let val e = new_ebind ()
      in
        all_psevars := e :: !all_psevars;
        let val IL.Free i = !e in print (Int.toString i) end;
        print "\n";
        IL.PSEvar e
      end
    

    (* actually, I think in situations where these are
       called it will be the case that there are no
       top-level "Bound"s *)
    fun same_evar r x =
        (case x of
             (Evar (ref (Bound t))) => same_evar r t
           | (Evar (r' as ref (Free _))) => r = r'
           | _ => false)

    (* FIX: delete this, no more priority evars *)
    fun same_wevar r x =
        (case x of
             (PEvar (ref (Bound t))) => same_wevar r t
           | (PEvar (r' as ref (Free _))) => r = r'
           | _ => false)

    exception Unify of string

    fun occurs (r : typ ebind ref) x =
        (case x of
             TVar _ => false
           | TRec stl => ListUtil.existsecond (occurs r) stl
           | Arrow (_, t1, t2) => List.exists (occurs r) t1 
                                  orelse occurs r t2
           | Arrows al => List.exists (fn (_, tl, t) =>
                                       List.exists (occurs r) tl
                                       orelse occurs r t) al
           | Sum (lcl) => 
                 ListUtil.existsecond (fn (Carrier {carried=t, ...}) => occurs r t | _ => false) lcl
           | Mu (_, vcl) => ListUtil.existsecond (occurs r) vcl
           | TRef c => occurs r c
           | TVec c => occurs r c
           | TCont c => occurs r c
           | TTag (t, _) => occurs r t
           | (Evar (ref (Bound t))) => occurs r t
           | (Evar (r' as ref (Free _))) => r = r'
           | TCmd (t, _, _) => occurs r t
           | TThread (t, _, _) => occurs r t
           | TPrio _ => false
           (* | TForall (_, _, t) => occurs r t (* FIX: delete this *) *)
(*           | At (t, w) => occurs r t
           | Shamrock (_, t) => occurs r t
           | TAddr w => false
 *)
        )

    (* occurs check for worlds is trivial, currently *)
    fun woccursw r w = false

    (* r := Bound t  with path compression. *)
    fun set r (Evar (ref (Bound t))) = set r t
      | set r t = r := Bound t

    (* FIX: delete this, no more priority evars *)
    fun wset r (PEvar (ref (Bound t))) = wset r t
      | wset r t = r := Bound t

    fun psset r (PSEvar (ref (Bound t))) = psset r t
      | psset r t = r := Bound t

    fun mapift (mt, _) v =
        case Variable.Map.find (mt, v) of
            NONE => v
          | SOME vv => vv

    fun mapifw (_, mw) v =
        case Variable.Map.find (mw, v) of
            NONE => v
          | SOME vv => vv

    fun mapplus m (v, vv) =
        Variable.Map.insert (m, v, vv)

    (* FIX: instead of `unifyex` now supertypex *)
    fun supertypex ctx eqmap t1 t2 =
	let val _ = Layout.print (Layout.listex
				      "supertype (" ")\n" ","
				      (map ILPrint.ttol [t1, t2]),
				  print)
	in
        (case (t1, t2) of
             (TVar v1, TVar v2) =>
                 ignore (Variable.eq (mapift eqmap v1, v2) 
                            orelse raise Unify "Var")

           | (TTag (t1, v1), TTag (t2, v2)) => 
                 let in
                     Variable.eq (mapift eqmap v1, v2) 
                      orelse raise Unify "tag var";
                     supertypex ctx eqmap t1 t2
                 end

           | (TVec t1, TVec t2) => supertypex ctx eqmap t1 t2
           | (TCont t1, TCont t2) => supertypex ctx eqmap t1 t2
           | (TRec lcl1, TRec lcl2) =>
                 let
                     val l = ListUtil.sort 
                              (ListUtil.byfirst String.compare) lcl1
                     val r = ListUtil.sort 
                              (ListUtil.byfirst String.compare) lcl2
                 in
                     ignore
                     (ListUtil.all2 (fn ((l1,t1),(l2,t2)) =>
                                     let in
                                         supertypex ctx eqmap t1 t2;
                                         l1 = l2
                                     end) l r
                      orelse raise Unify "Record")
                 end
           | (Arrow (_, dom1, cod1), Arrow (_, dom2, cod2)) => 
                 let in
                     ListUtil.all2 (fn (a, b) => (supertypex ctx eqmap b a; (* FIX: domain is contravariant *) 
                                                  true)) 
                                        dom1 dom2
                        orelse raise Unify "Arrow domains have different arity";
                     supertypex ctx eqmap cod1 cod2
                 end
           | (TRef c1, TRef c2) => supertypex ctx eqmap c1 c2
           | (Mu (i1, m1), Mu (i2, m2)) => 
               let val (mt, mw) = eqmap
               in
                 ignore
                 ((i1 = i2 andalso
                   ListUtil.all2 (fn ((v1, t1),
                                     (v2, t2)) =>
                                 (supertypex ctx (mapplus mt (v1, v2), mw) t1 t2; 
                                  true)) m1 m2)
                  orelse raise Unify "mu")
               end
           | (Sum ltl1, Sum ltl2) =>
                 ignore
                 ((ListUtil.all2 (fn ((l1, t1),
                                      (l2, t2)) =>
                                  ((case (t1, t2) of
                                      (NonCarrier, NonCarrier) => ()
                                    | (Carrier { definitely_allocated = aa1, carried = tt1}, 
                                       Carrier { definitely_allocated = aa2, carried = tt2}) => 
                                        let in
                                          if aa1 = aa2 then ()
                                          else raise Unify "sum:always_allocated(bug!)";
                                          supertypex ctx eqmap tt1 tt2
                                        end
                                    | _ => raise Unify "sum:carrier");
                                      l1 = l2))
                  (ListUtil.sort (ListUtil.byfirst String.compare) ltl1)
                  (ListUtil.sort (ListUtil.byfirst String.compare) ltl2))
                  orelse raise Unify "sum")
(*
           | (TAddr w1, TAddr w2) => unifywex ctx eqmap w1 w2
           | (Shamrock (w1, t1), Shamrock (w2, t2)) => 
                 (* this binds world variables, so we need to insert those in
                    another map... *)
                 let val (mt, mw) = eqmap
                 in supertypex ctx (mt, mapplus mw (w1, w2)) t1 t2
                 end
           | (At (t1, w1), At (t2, w2)) =>
                 let in
                     supertypex ctx eqmap t1 t2;
                     unifywex ctx eqmap w1 w2
                 end
*)
           | (Arrows al1, Arrows al2) =>
                 let in
                   if length al1 <> length al2 then raise Unify "Arrows have different arity"
                   else ();
                   ListPair.app (fn ((_, dom1, cod1), (_, dom2, cod2)) =>
                                 let in
                                   ListUtil.all2 (fn (a, b) => (supertypex ctx eqmap b a; (* FIX: domain is contravariant *) 
                                                                true)) 
                                   dom1 dom2
                                   orelse raise Unify "(inner) Arrows have different arity";

                                   supertypex ctx eqmap cod1 cod2
                                 end) (al1, al2)
                 end
           | (TCmd (t1, (pi1, pp1, pf1), cc1), TCmd (t2, (pi2, pp2, pf2), cc2)) =>
               (* unified psconstraints from TThread *)
               let val unified_cc = (pscstr_sup pi2 pi1) (* FIX: start refinement contravariant *)
                                    @ (pscstr_sup pp1 pp2)
                                    @ (pscstr_sup pf1 pf2)
                                    @ (!cc1) 
                                    @ (!cc2) 
               in
                 cc1 := unified_cc;
                 cc2 := unified_cc;
                 supertypex ctx eqmap t1 t2
               end
           | (TThread (t1, ps1, cc1), TThread (t2, ps2, cc2)) =>
               (* unified psconstraints from TThread *)
               let val unified_cc = (pscstr_sup ps1 ps2)
                                    @ (!cc1)
                                    @ (!cc2)
               in
                 cc1 := unified_cc;
                 cc2 := unified_cc;
                 supertypex ctx eqmap t1 t2
               end
            | (TPrio ps1, TPrio ps2) =>
              (* FIXED: unify priorities *)
	          let val cc = pscstr_sup ps1 ps2
              in
                  global_cstrs := cc @ !global_cstrs
              end
            
            | (Evar (ref (Bound t1)), t2) => supertypex ctx eqmap t1 t2
            | (t1, Evar (ref (Bound t2))) => supertypex ctx eqmap t1 t2
            | (Evar (r as ref (Free _)), t2) =>
                if same_evar r t2 then ()
                else if occurs r t2 then
                    raise Unify "circularity"
                else 
                    (case t2 of
                        (TPrio s) => 
                        let val ps as PSEvar r' = new_psevar ()
                            val cc = pscstr_sup ps s
                        in
                            global_cstrs := cc @ !global_cstrs;
                            set r (TPrio (ps))
                        end
                        | _ => set r t2)
            | (t1, Evar (r as ref (Free _))) =>
                if same_evar r t1 then ()
                else if occurs r t1 then
                    raise Unify "circularity"
                else 
                    (case t1 of
                        (TPrio s) => 
                        let val ps as PSEvar r' = new_psevar ()
                            val cc = pscstr_sup s ps
                        in
                            global_cstrs := cc @ !global_cstrs;
                            set r (TPrio (ps))
                        end
                        | _ => set r t1)
           (* | (TForall (vs1, cs1, t1), TForall (vs2, cs2, t2)) =>
             let val (mt, mw) = eqmap
                 val mw' = ListPair.foldl (fn (v1, v2, m) => mapplus m (v1, v2))
                                      mw (vs1, vs2)
             in
                 supertypex ctx (mt, mw') t1 t2
             end (* FIX: delete this *) *)
(*
           | (Shamrock _, _) => raise Unify "tycon mismatch (shamrock)"
           | (_, Shamrock _) => raise Unify "tycon mismatch (shamrock)"
           | (Arrows _, _) => raise Unify "tycon mismatch (arrows)"
           | (_, Arrows _) => raise Unify "tycon mismatch (arrows)"
           | (TAddr _, _) => raise Unify "tycon mismatch (addr)"
           | (_, TAddr _) => raise Unify "tycon mismatch (addr)"
*)
           | (Sum _, _) => raise Unify "tycon mismatch (sum)"
           | (_, Sum _) => raise Unify "tycon mismatch (sum)"
           | (Mu _, _) => raise Unify "tycon mismatch (mu)"
           | (_, Mu _) => raise Unify "tycon mismatch (mu)"
           | (TRef _, _) => raise Unify "tycon mismatch (ref)"
           | (_, TRef _) => raise Unify "tycon mismatch (ref)"
           | (Arrow _, _) => raise Unify "tycon mismatch (arrow)"
           | (_, Arrow _) => raise Unify "tycon mismatch (arrow)"
           | (TCont _, _) => raise Unify "tycon mismatch (cont)"
           | (_, TCont _) => raise Unify "tycon mismatch (cont)"
           | (TVec _, _) => raise Unify "tycon mismatch (vec)"
           | (_, TVec _) => raise Unify "tycon mismatch (vec)"
           | (TTag _, _) => raise Unify "tycon mismatch (tag)"
           | (_, TTag _) => raise Unify "tycon mismatch (tag)"
           | (TVar _, _) => raise Unify "tycon mismatch (var)"
           | (_, TVar _) => raise Unify "tycon mismatch (var)"
           | (TRec _, _) => raise Unify "tycon mismatch (record)"
           | (_, TRec _) => raise Unify "tycon mismatch (record)"
           | (TCmd _, _) => raise Unify "tycon mismatch (command)"
           | (_, TCmd _) => raise Unify "tycon mismatch (command)"
           | (TThread _, _) => raise Unify "tycon mismatch (thread)"
           | (_, TThread _) => raise Unify "tycon mismatch (thread)"
           | (TPrio _, _) => raise Unify "tycon mismatch (prio)"
           | (_, TPrio _) => raise Unify "tycon mismatch (prio)"
           (* | (TForall _, _) => raise Unify "tycon mismatch (forall)" (* FIX: delete this *) *)
           (* | (_, TForall _) => raise Unify "tycon mismatch (forall)" (* FIX: delete this *) *)
(*           | (At _, _) => raise Unify "tycon mismatch (at)"
           | (_, At _) => raise Unify "tycon mismatch (at)" *)

                 (* no catch-all; dangerous if missing cases of unification! *)
        )
	end

    (* and unifypex ctx eqmap w1 w2 =
      case (w1, w2) of
        (PVar a, PVar b) => ignore (Variable.eq (mapifw eqmap a, b) orelse raise Unify "world var")

      | (PConst a, PConst b) => ignore (a = b orelse raise Unify "prio const")
      | (PVar _, PConst _) => raise Unify "prio var/const"
      | (PConst _, PVar _) => raise Unify "prio const/var"
      (* if either is bind, path compress... *)
      | (PEvar (ref (Bound w1)), w2) => unifypex ctx eqmap w1 w2
      | (w1, PEvar (ref (Bound w2))) => unifypex ctx eqmap w1 w2

      | (PEvar (r as ref (Free _)), w2) =>
          if same_wevar r w2 then ()
          else if woccursw r w2 
               then raise Unify "circularity"
               else wset r w2
      | (w1, PEvar (r as ref (Free _))) =>
          if same_wevar r w1 then ()
          else if woccursw r w1 
               then raise Unify "circularity"
               else wset r w1 *)

    fun supertype ctx t1 t2  = 
      supertypex ctx (Variable.Map.empty, Variable.Map.empty) t1 t2

    fun unify ctx t1 t2  = 
      (supertypex ctx (Variable.Map.empty, Variable.Map.empty) t1 t2;
      supertypex ctx (Variable.Map.empty, Variable.Map.empty) t2 t1)

    (* fun unifyp ctx w1 w2 = unifypex ctx (Variable.Map.empty, Variable.Map.empty) w1 w2 *)

end
