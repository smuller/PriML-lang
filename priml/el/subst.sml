
structure Subst =
struct

  open IL

  structure E = EL

  exception Subst of string


  fun fromlist l =
      foldl VM.insert' VM.empty l

  (* XXX5 these should be in IL *)
  (* t/x in t *)
  fun tsubst s (x as (TVar v)) =
      (case VM.find (s, v) of
           SOME tt => tt
         | NONE => x)
    | tsubst s (TRec ltl) = TRec (ListUtil.mapsecond (tsubst s) ltl)
    | tsubst s (Arrow a) = Arrow (arrow s a)
    | tsubst s (Sum ltl) = Sum (ListUtil.mapsecond (arminfo_map (tsubst s)) ltl)
    | tsubst s (Mu (i, vtl)) =
           let (* remove bindings for each variable *)
               val ns = foldl (fn ((v,_), s) => 
                               VM.insert (s, v, TVar v)) s vtl
           in  Mu (i, ListUtil.mapsecond (tsubst ns) vtl)
           end
    | tsubst s (Evar(ref (Bound t))) = tsubst s t
    | tsubst s (x as (Evar _)) = x

    | tsubst s (TRef t) = TRef (tsubst s t)

    | tsubst s (TVec t) = TVec (tsubst s t)
    | tsubst s (TCont t) = TCont (tsubst s t)

    | tsubst s (TTag (t, v)) = TTag (tsubst s t, v)
    | tsubst s (Arrows l) = Arrows (map (arrow s) l)
    | tsubst s (TCmd (t, p)) = TCmd (tsubst s t, p)
    | tsubst s (TThread (t, p)) = TThread (tsubst s t, p)
    | tsubst s (TPrio p) = TPrio p
    (* | tsubst s (TForall (vs, cs, t)) = TForall (vs, cs, tsubst s t) (* FIX: delete this *) *)
(*
    | tsubst s (At (t, w)) = At (tsubst s t, w)
    | tsubst s (Shamrock (wv, t)) = Shamrock (wv, tsubst s t)
    | tsubst s (TAddr w) = TAddr w
*)

  and arrow s (b, dom, cod) =
      (b, map (fn (v, t) => (v, tsubst s t)) dom, tsubst s cod)

  fun etsubst s t =
      (case t of
           (x as E.TVar v) =>
               (case StringMap.find (s, v) of
                    SOME tt => tt
                  | NONE => x)
         | E.TNum n => t
         | E.TApp (tl, str) => E.TApp (map (etsubst s) tl, str)
         | E.TRec stl => E.TRec (ListUtil.mapsecond (etsubst s) stl)
(*          | E.TAddr s => t *)
         | E.TArrow (dom, cod) => E.TArrow(etsubst s dom, etsubst s cod)
         | E.TCmd (t, p) => E.TCmd (etsubst s t, p)
         | E.TThread (t, p) => E.TThread (etsubst s t, p)
         | E.TPrio p => E.TPrio p)
         (* | E.TForall (vs, t) => E.TForall (vs, etsubst s t) (* FIX: delete this *) *)


  (* w/x in t *)
  fun prsubst (s: prio subst) (x as (TVar v)) = x
    | prsubst s (TRec ltl) = TRec (ListUtil.mapsecond (prsubst s) ltl)
    | prsubst s (Arrow a) = Arrow (warrow s a)
    | prsubst s (Arrows l) = Arrows (map (warrow s) l)
    | prsubst s (Sum ltl) = Sum (ListUtil.mapsecond (arminfo_map (prsubst s)) ltl)
    | prsubst s (Mu (i, vtl)) = Mu (i, ListUtil.mapsecond (prsubst s) vtl)
    | prsubst s (Evar(ref (Bound t))) = prsubst s t
    | prsubst s (x as (Evar _)) = x

    | prsubst s (TRef t) = TRef (prsubst s t)

    | prsubst s (TVec t) = TVec (prsubst s t)
    | prsubst s (TCont t) = TCont (prsubst s t)

    | prsubst s (TTag (t, v)) = TTag (prsubst s t, v)

    | prsubst s (TCmd (t, (pi, pp, pf))) = 
        TCmd (prsubst s t, (prsubsps s pi, prsubsps s pp, prsubsps s pf))

    | prsubst s (TThread (t, ps)) = 
        TThread (prsubst s t, prsubsps s ps)
    | prsubst s (TPrio ps) = 
        TPrio (prsubsps s ps)

    (* | prsubst s (TForall (wvs, cs, t)) =
      let val nvs = List.map Variable.alphavary wvs
          val t' = prsubst (fromlist (ListPair.zip (wvs, List.map PVar nvs))) t
          val cs' = cs (* XXX4 substitute in constraints *)
      in
          TForall (nvs, cs', prsubst s t')
      end (* FIX: delete this *) *)
  (*
    | prsubst s (TAddr w) = TAddr (wsubsw s w)
    | prsubst s (x as Shamrock (wv, t)) = 
      let val nv = Variable.alphavary wv
          val t' = prsubst (fromlist [(wv, WVar nv)]) t
      in Shamrock(wv, prsubst s t')
      end
    | prsubst s (At (t, w)) = At (prsubst s t, wsubsw s w)
*)

  and warrow s (b, dom, cod) =
      (b, map (fn (v, t) => (v, prsubst s t)) dom, prsubst s cod)

  (* w/x in w' *)
  and prsubsp (s: prio subst) x : prio =
      case x of
          PVar v =>
          ((* print ("subbing for " ^ (Variable.show v) ^ "\n"); *)
           case VM.find (s, v) of
               SOME ww => ww 
             | NONE => x)
        | PEvar(ref (Bound w)) => prsubsp (s: prio subst) w
        | PEvar _ => x
        | PConst _ => x

  and prsubsps (s: prio subst) x : prioset =
      case x of 
           PSSet ps => PSSet (PrioSet.map (prsubsp s) ps)
         | PSEvar (ref (Bound w)) => prsubsps s w
         | _ => x

		    (*
  and prsubspsc s (PSSup (ps1, ps2))  = PSSup (prsubsps s ps1, prsubsps s ps2)
    | prsubspsc s (PSCons (ps1, ps2)) = PSCons (prsubsps s ps1, prsubsps s ps2)
		    *)
  and prsubsc s (PCons (p1, p2)) = (PCons (prsubsp s p1, prsubsp s p2))

  fun pbinds  E.PWild _ = false
    | pbinds (E.PAs (i, p)) v = i = v orelse pbinds p v
    | pbinds (E.PConstrain (p, t)) v = pbinds p v
    | pbinds (E.PConstant _) _ = false
    | pbinds (E.PVar i) v = i = v
    | pbinds (E.PRecord lpl) v = 
      ListUtil.existsecond (fn p => pbinds p v) lpl
    | pbinds (E.PApp  (_, SOME p)) v = pbinds p v
    | pbinds (E.PApp  (_, NONE)) v = false
    | pbinds (E.PWhen (_, p)) v = pbinds p v

  (* exp/var in exp'. assumes exp closed. *)
     
  fun esubst (s as (vv : string, ee : EL.exp_)) (e,loc) =
      (fn x => (x, loc))
      (case e of
           E.Var (E.Id v) => if v = vv then ee else e
         | E.Var _ => e
         | E.Constant _ => e
         | E.Float _ => e
         | E.Primapp (l, ts, es) => E.Primapp(l, ts, map (esubst s) es)
         | E.Proj (l,t,e) => E.Proj (l, t, esubst s e)
         | E.Record lel => E.Record (ListUtil.mapsecond (esubst s) lel)
         | E.Seq (a,b) => E.Seq (esubst s a, esubst s b)
         | E.Let (d,e) =>
               let val (d, shadowed) = dsubst s d
               in E.Let (d, if shadowed then e else esubst s e)
               end
(*
         | E.Throw (a, b) => E.Throw(esubst s a, esubst s b)
         | E.Letcc (v, e') =>
               if v = vv 
               then e
               else E.Letcc(v, esubst s e')
*)
         | E.App (a,b,i) => E.App (esubst s a, esubst s b, i)

         | E.Andalso (a,b) => E.Andalso (esubst s a, esubst s b)
         | E.Orelse (a,b) => E.Orelse (esubst s a, esubst s b)
         | E.Andthen (a,b) => E.Andthen (esubst s a, esubst s b)
         | E.Otherwise (a,b) => E.Otherwise (esubst s a, esubst s b)
         | E.If (a,b,c) => E.If (esubst s a, esubst s b, esubst s c)

         | E.Constrain (e,t) => E.Constrain (esubst s e, t)
         | E.Case (el, pel, NONE) => E.Case (map (esubst s) el, 
                                             map (mlsubst s) pel, NONE)
         | E.Case _ => raise Subst "case SOME"
         | E.Raise e => E.Raise (esubst s e)
(*
         | E.Say (imports, e) => E.Say (imports, 
                                        (* check shadowing... *)
                                        if List.exists (fn (_, v) => v = vv) imports
                                        then e
                                        else esubst s e)
*)
         | E.Handle (e, pel) => E.Handle (esubst s e, map (msubst s) pel)
(*
         | E.Jointext el => E.Jointext (map (esubst s) el)
*)
         | E.Vector el => E.Vector (map (esubst s) el)
         | E.CompileWarn s => E.CompileWarn s
(*         | E.Get (a,b) => E.Get(esubst s a, esubst s b)
 *)
     )


  (* pattern lists as in fn; 
     just pretend it's a tuple for the sake of bindings *)
  (* XXX is this accurate? are earlier args available in the 'when' 
     clauses for pats in later args? *)
  and fsubst (s as (vv, ee)) (pl,e) =
      if pbinds (E.PRecord (map (fn p => ("", p)) pl)) vv then (pl, e)
      else (map (psubst s) pl, esubst s e)

  and mlsubst (s as (vv, ee)) (pl, e) =
      if List.exists (fn p => pbinds p vv) pl
      then (map (psubst s) pl, e)
      else (map (psubst s) pl, esubst s e)

  and psubst s (E.PWild) = E.PWild
    | psubst s (E.PAs (i, p)) = E.PAs (i, psubst s p)
    | psubst s (E.PConstrain (p, t)) = E.PConstrain(psubst s p, t)
    | psubst s (E.PConstant c) = E.PConstant c
    | psubst s (E.PVar i) = E.PVar i
    | psubst s (E.PRecord lpl) = 
    E.PRecord (ListUtil.mapsecond (psubst s) lpl)
    | psubst s (E.PApp  (t, p)) = E.PApp (t, Option.map (psubst s) p)
    | psubst s (E.PWhen (e, p)) = E.PWhen (esubst s e, psubst s p)

  (* substitute in a match (pattern * expression), but only if the
     pattern doesn't shadow the variable in question. *)
  and msubst (s as (vv, ee)) (p, e) =
      if pbinds p vv then (psubst s p, e)
      else (psubst s p, esubst s e)

  (* substitute in a declaration, and return a boolean indicating if the
     (term) variable was shadowed in the decl. *)

  and dsubst (s as (vv,ee)) ((d,loc) : E.dec) =
      (fn (x,b) => ((x, loc), b))
      (case d of
           E.Val (tyvars, p, e) => (E.Val (tyvars, psubst s p, esubst s e), 
                                        pbinds p vv)
         | E.Signature (i, ss) => (d, i = vv)
         | E.Structure (i, ss) => (d, i = vv)
         | E.SigVal (i, _) => (d, i = vv)
         | E.SigType (i, _) => (d, false)
         | E.Do e => (E.Do (esubst s e), false)
         | E.Fun { inline, funs = l } => 
               (* if any function is named the same as this variable,
                 do no substitution and return shadowed. *)
               if List.exists (fn (_, f, _) => f = vv) l then (d, true)
               else let
                        fun dfs (pl, to, e) =
                            if pbinds (E.PRecord (map (fn x => 
                                                       ("", x)) pl)) vv 
                            then (map (psubst s) pl, to, e)
                            else (map (psubst s) pl, to, esubst s e)
                    in (E.Fun { inline = inline,
                                funs = (map (fn (tyvars, f, branches) => 
                                             (tyvars, f, map dfs branches)) l) }, false)
                    end
         | E.Datatype (_, dl) =>
               (* datatypes have no expressions, 
                  but bind some constructors *)
               let fun one (_, ctors) = 
                   List.exists (fn (i,_) => i = vv) ctors
               in (d, List.exists one dl)
               end
         (* these are simple *)
         | E.Exception (i, _) => (d, i = vv)
         | E.Tagtype t => (d, false)
         | E.Newtag (i, _, _) => (d, i = vv)
         | E.Type _ => (d, false)
(*
         | E.ExternType _ => (d, false)
         | E.ExternVal (tv, id, t, w, l) => (d, id = vv)
         | E.ExternWorld (w, _) => (d, false)
*)
      )

end
