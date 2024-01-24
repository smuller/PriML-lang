
structure Context :> CONTEXT =
struct

    (* FIXING: moving PSetCstrs to Context *)

    (* open IL   *)
    open PSContext

    exception PSConstraints of string

    (* PRIORITY SET CONSTRAINTS *)
    (* add superset *)
    fun pscstr_sup ws1 ws2 = [IL.PSSup (ws1, ws2)]

    (* add constraint *)
    fun pscstr_cons ws1 ws2 = [IL.PSCons (ws1, ws2)]

    (* add equal *)
    fun pscstr_eq ws1 ws2 = (pscstr_sup ws1 ws2) 
                            @ (pscstr_sup ws2 ws1)

    (* add general constraint:
    *   pi = set of initial priorities
    *   pp = set of all possible priorities
    *   pf = set of final priorities
    *   general constraints: pp is superset of pi, pp is superset of pf
    * *)
    (* FIX: pp not superset of pi *)
    fun pscstr_gen pi pp pf = (pscstr_sup pp pi) 
                              @
                              (pscstr_sup pp pf)


    (* SOLVER FUNCTIONS *)
    (* priority set constraints solver *)

    (* check if s1 is superset of s2 *)
    fun check_sup (s1, s2) = 
      IL.PrioSet.equal (IL.PrioSet.difference (s2, s1), IL.PrioSet.empty)

    

    fun solve_pscstrs (psctx: pscontext) (pscstrs: psconstraint list) = 
      let 
        (* retrieve priority of psevar in pscontext. 
         * If psevar is not in pscontext with empty set as the value. *)
        fun getps (psctx, pse) = 
          case PSEvarMap.find (psctx, pse) of 
               SOME s => (psctx, s)
             | NONE => (PSEvarMap.insert (psctx, pse, IL.PrioSet.empty), IL.PrioSet.empty)

        (* solve priority set system from IL.PSSup (s1, s2) constraints, skip IL.PSCons.
         * If s1 is not the superset of s2, add every priorities in s2 to s1. *)
        fun solve (cstr, psctx) = 
          case cstr of 
            IL.PSCons (IL.PSSet _, IL.PSSet _) => psctx
          | IL.PSCons (IL.PSSet _, ps as IL.PSEvar _) => 
              let val (psctx', _) = getps (psctx, ps) 
              in 
                psctx'
              end
          | IL.PSCons (ps as IL.PSEvar _, IL.PSSet _) =>
              let val (psctx', _) = getps (psctx, ps) 
              in 
                psctx'
              end
          | IL.PSCons (ps1 as IL.PSEvar _, ps2 as IL.PSEvar _) =>
              let val (psctx', _) = getps (psctx, ps1) 
                  val (psctx'', _) = getps (psctx', ps2)
              in
                psctx''
              end

          | IL.PSSup (IL.PSSet _, IL.PSSet _) => psctx
          | IL.PSSup (IL.PSSet _, ps as IL.PSEvar _) =>
              let val (psctx', _) = getps (psctx, ps) 
              in 
                psctx'
              end
          | IL.PSSup (ps as IL.PSEvar _, IL.PSSet s) => 
              let val (psctx', s') = getps (psctx, ps)
              in
                if check_sup (s', s) then psctx'
                else PSEvarMap.insert (psctx', ps, IL.PrioSet.union(s', s))
              end
          | IL.PSSup (ps1 as IL.PSEvar _, ps2 as IL.PSEvar _) =>
              let val (psctx', s1) = getps (psctx, ps1) 
                  val (psctx'', s2) = getps (psctx', ps2)
              in
                if check_sup (s1, s2) then psctx''
                else PSEvarMap.insert (psctx'', ps1, IL.PrioSet.union(s1, s2))
              end
        in 
        let val psctx' = List.foldl solve psctx pscstrs 
        in
          if PSEvarMap.collate IL.PrioSet.compare (psctx', psctx) = EQUAL then psctx'
          else solve_pscstrs psctx' pscstrs
        end
      end


    






    open Variable

    val showbinds = Params.flag false
        (SOME ("-showilbinds",
               "When ")) "showilbinds"
        
    structure S = StringMap
    structure SU = StringMapUtil
    structure SS = StringSet
    structure SSU = StringSetUtil
    structure VS = Variable.Set
    structure VSU = Variable.SetUtil
    structure VM = Variable.Map
    structure E = EL

    (* first is class of identifier, second is identifier *)
    exception Context of string
    exception Absent of string * string

    (* FIXING: global constraints for priorities (instead of one for each priority)
            moved from Unify.sml *)
    val global_cstrs = ref []

    val assumed = ref []

    val new_evar = ref (fn _ => raise (Context "not installed"))
    fun install_ne f =
        new_evar := f

    fun absent what s =
        let in 
(*
              print "(Unbound in context: ";
              print s;
              print ")\n";
*)
            raise Absent (what, s)
        end

    type tpcons = (VS.set * SS.set) VM.map * (VS.set * SS.set) S.map

    val tpc_empty =
        (VM.empty, S.empty)

    fun ground (IL.PEvar r) =
        (case !r of
             IL.Free _ => raise (Context "prio not constant or variable")
           | IL.Bound x => x)
      | ground p = p

    fun tpc_insert (vm, sm) (IL.PConst s1, IL.PConst s2) =
        (case S.find (sm, s1) of
             SOME (vs, ss) => (vm, S.insert (sm, s1, (vs, SS.add (ss, s2))))
           | NONE => (vm, S.insert (sm, s1, (VS.empty, SS.add (SS.empty, s2)))))
      | tpc_insert (vm, sm) (IL.PVar v1, IL.PConst s2) =
        (case VM.find (vm, v1) of
             SOME (vs, ss) => (VM.insert (vm, v1, (vs, SS.add (ss, s2))), sm)
           | NONE => (VM.insert (vm, v1, (VS.empty, SS.add (SS.empty, s2))), sm))
      | tpc_insert (vm, sm) (IL.PConst s1, IL.PVar v2) =
        (case S.find (sm, s1) of
             SOME (vs, ss) => (vm, S.insert (sm, s1, (VS.add (vs, v2), ss)))
           | NONE => (vm, S.insert (sm, s1, (VS.add (VS.empty, v2), SS.empty))))
      | tpc_insert (vm, sm) (IL.PVar v1, IL.PVar v2) =
        (case VM.find (vm, v1) of
             SOME (vs, ss) => (VM.insert (vm, v1, (VS.add (vs, v2), ss)), sm)
           | NONE => (VM.insert (vm, v1, (VS.add (VS.empty, v2), SS.empty)), sm))
      | tpc_insert (vm, sm) _ = raise (Context "prio cons not constant or variable")

    fun tpc_mem (vm, sm) (IL.PConst s1, IL.PConst s2) =
        (case S.find (sm, s1) of
             SOME (_, ss) => SS.member (ss, s2)
           | NONE => false)
      | tpc_mem (vm, sm) (IL.PVar v1, IL.PConst s2) =
        (case VM.find (vm, v1) of
             SOME (_, ss) => SS.member (ss, s2)
           | NONE => false)
      | tpc_mem (vm, sm) (IL.PConst s1, IL.PVar v2) =
        (case S.find (sm, s1) of
             SOME (vs, _) => VS.member (vs, v2)
           | NONE => false)
      | tpc_mem (vm, sm) (IL.PVar v1, IL.PVar v2) =
        (case VM.find (vm, v1) of
             SOME (vs, _) => VS.member (vs, v2)
           | NONE => false)
      | tpc_mem (vm, sm) _ = raise (Context "prio cons not constant or variable")

    fun get_greater ((_, sm): tpcons) (IL.PConst s) =
        (case S.find (sm, s) of
             SOME (vs, ss) => (List.map IL.PVar (VSU.tolist vs)) @
                              (List.map IL.PConst (SSU.tolist ss))
           | NONE => [])
      | get_greater ((vm, _): tpcons) (IL.PVar v) =
        (case VM.find (vm, v) of
             SOME (vs, ss) => (List.map IL.PVar (VSU.tolist vs)) @
                              (List.map IL.PConst (SSU.tolist ss))
           | NONE => [])
      | get_greater _ _ =
        raise (Context "prio not constant or variable")

    datatype context = 
        (* plabs = priority labels *)
        C of { vars : (IL.typ IL.poly * Variable.var * IL.idstatus) S.map,
               cons : (IL.kind * IL.con * IL.tystatus) S.map,
               plabs : SS.set,
               mobiles : VS.set,
               pcons : (IL.prio * IL.prio) list,
               tpcons : tpcons,
               (* obsolete, but might come back *)
               dbs : unit S.map,
               sign: context S.map }



    structure L = Layout

    fun ctol (C { vars, cons, plabs, mobiles, pcons, tpcons, dbs, sign }) =
      let
        val $ = L.str
        val % = L.mayAlign
        val itos = Int.toString

        val vars = S.listItemsi vars
      in
        %[$"",
          L.indent 3
          (
           %[$"vars:",
             % (map (fn (s, (tp, v, vs)) =>
                     %[%[$s, $"==", $(Variable.tostring v), $":"],
                       L.indent 2 (%[ILPrint.ptol ILPrint.ttol tp])]) vars),
             $"XXX mobiles, cons, plabs"])]
          
      end

    (* for type evars. these can only appear in the types of vars. *)
    fun has_evar (C{vars, ...}) n =
      let
          open IL
          fun has tt =
              (case tt of
                   TVar _ => false
                 | TRec ltl => List.exists (fn (_, t) => 
                                            has t) ltl
                 | Arrow (_, tl, t) =>
                       has t orelse
                       List.exists has tl
                 | Sum ltl => List.exists 
                       (fn (_, Carrier { carried, ... }) => has carried
                          | _ => false) ltl
                 | Mu (_, vtl) => List.exists (fn (_, t) => has t) vtl
                 | Evar (ref (Free m)) => n = m
                 | Evar (ref (Bound t)) => has t
                 | TVec t => has t
                 | TCont t => has t
                 | TTag (t, _) => has t
                                      (*
                 | At (t, w) => has t
                 | Shamrock (_, t) => has t
                 | TAddr _ => false
*)
                 | Arrows l =>
                       List.exists (fn (_, tl, t) =>
                                    has t orelse List.exists has tl) l
                 | TRef t => has t
                 | TCmd (t, _, _) => has t
                 | TThread (t, _, _) => has t
                 | TPrio _ => false) (* FIX: refinements don't have evars? *)
                 (* | TForall (_, _, t) => has t (* FIX: delete this *) *)
      in
        SU.exists (fn (Poly({tys}, t), _, _) => has t) vars 
      end

    (* for world evars. Again, these can only appear in the types of bound vars;
       bound worlds and types have uninteresting kinds. *)
    fun has_wevar (C{vars, ...}) n =
      let
          open IL
          fun hasw (PVar _) = false
            | hasw (PConst _) = false
            | hasw (PEvar er) =
            case !er of
              Free m => m = n
            | Bound w => hasw w

          and has tt =
              (case tt of
                   TVar _ => false
                 | TRec ltl => List.exists (fn (_, t) => 
                                            has t) ltl
                 | Arrow (_, tl, t) =>
                       has t orelse
                       List.exists has tl
                 | Sum ltl => List.exists 
                       (fn (_, Carrier { carried, ... }) => has carried
                          | _ => false) ltl
                 | Mu (_, vtl) => List.exists (fn (_, t) => has t) vtl
                 | Evar (ref (Free _)) => false
                 | Evar (ref (Bound t)) => has t
                 | TVec t => has t
                 | TCont t => has t
                 | TTag (t, _) => has t
(*
                 | At (t, w) => has t orelse hasw w
                 | Shamrock (_, t) => has t
                 | TAddr w => hasw w
*)
                 | Arrows l =>
                       List.exists (fn (_, tl, t) =>
                                    has t orelse List.exists has tl) l
                 | TRef t => has t
                 | TCmd (t, _, _) => has t
                 | TThread (t, _, _) => has t
                 | TPrio _ => false)
                 (* | TForall (_, _, t) => has t (* FIX: delete this *) *)

      in
        SU.exists (fn (Poly({tys}, t), _, _) => has t) vars
      end

    (* Worlds may be world variables or world constants. If there is a world
       constant we assume it takes precedence. (It might be good to prevent
       the binding of a world variable when there is a constant of the same
       name?) *)
    fun prio (C{plabs, ...}) s =
      (* if SS.member (plabs, s)
      then IL.PConst s
      else
        (case S.find (s) of
           SOME x => IL.PVar x
         | NONE => absent "prios" s) *)

      (* FIX: priorities should be variables *)

      if SS.member (plabs, s)
      then IL.PConst s
      else absent "plabs" s


    fun varex (C {vars, ...}) sym =
        (case S.find (vars, sym) of
             SOME x => x
           | NONE =>
             ( (* we'll assume this is defined elsewhere *)
               let val tt = (!new_evar) ()
                   val v = Variable.namedvar sym
               in
                   assumed := (sym, tt)::(!assumed);
                   (IL.Poly({tys = nil}, tt), v, IL.Normal)
               end))

    fun var ctx sym = varex ctx sym

    fun conex (C {cons, ...}) module sym =
        (case S.find (cons, sym) of
             SOME x => x
           | NONE => absent "cons" sym)
            (* ( (* we'll assume this is defined elsewhere *)
               let val tt = (!new_evar) ()
                   val v = Variable.namedvar sym
               in
                   assumed := (sym, tt)::(!assumed);
                   (0, IL.Typ (IL.TVar v), IL.Regular)
               end)) *)

    fun con ctx sym = conex ctx NONE sym

    fun bindplab (C {vars, cons, dbs, plabs, pcons, tpcons, mobiles, sign }) sym =
        C { vars = vars,
            cons = cons,
            plabs =
            (if SS.member (plabs, sym) then plabs
             else SS.add(plabs, sym)),
            mobiles = mobiles,
            pcons = pcons,
            tpcons = if sym = "bot" then tpcons
                     else (tpc_insert tpcons (IL.PConst "bot", IL.PConst sym)),
            dbs = dbs,
            sign = sign }

    fun bindex (C {vars, cons, dbs, plabs, pcons, tpcons, mobiles, sign }) sym typ var stat =
      (* TRYING:  
            add x : TPrio[y :: y = x] to ctx
            add global constraint: { x } is a subset of R
        *)
      let 
        val sym = (case sym of NONE => 
                     ML5pghUtil.newstr "bindex" | SOME s => s)
        val IL.Poly ({tys}, t) = typ
        val t' = 
            case t of
                IL.TPrio ps => 
                    (* FIX: add x : TPrio[y :: y = x] to ctx *)
                    (* FIX^^^: add priority_name : TPrio[{priority_name}] to ctx *)
                    (* Q: ? *)
                    let val p' = IL.PConst sym
                        val ps' = IL.PSSet (IL.PrioSet.singleton p')

                        val cc = pscstr_sup ps ps'
                    in
                        global_cstrs := cc @ !global_cstrs;
                        IL.TPrio ps'
                    end
              | _ => t

      in
        if !showbinds
        then let in
          print (sym ^ " == " ^ Variable.tostring var ^ " : ");
          Layout.print(ILPrint.ptol ILPrint.ttol typ, print);
          print "\n"
             end
        else ();
        C { vars = S.insert (vars, 
                             sym,
                             (IL.Poly ({tys = tys}, t'), var, stat)),
            cons = cons,
            plabs = plabs,
            mobiles = mobiles,
            pcons = pcons,
            tpcons = tpcons,
            dbs = dbs,
            sign = sign }
      end

    fun bindv c sym t v = bindex c (SOME sym) t v IL.Normal

    fun bindu c sym typ var stat = bindex c (SOME sym) typ var stat

    fun bindcex (C { cons, vars, dbs, mobiles, pcons, tpcons, plabs, sign }) module sym con kind status =
        C { vars = vars,
            cons = S.insert (cons, sym, (kind, con, status)),
            plabs = plabs,
            mobiles = mobiles,
            pcons = pcons,
            tpcons = tpcons,
            dbs = dbs,
            sign = sign }

    fun bindc c sym con kind status = bindcex c NONE sym con kind status

    (* fun bindp (C { cons, vars, dbs, mobiles, pcons, tpcons, plabs, sign }) s v =
        C { vars = vars,
            cons = cons,
            mobiles = mobiles,
            plabs = plabs,
            pcons = pcons,
            tpcons = (tpc_insert tpcons (IL.PConst "bot", IL.PVar v)),
            prios = S.insert (s, v),
            dbs = dbs,
            sign = sign } *) (* FIX: delete priority variables *)

          (* Kind of inefficient, but we do a DFS at every check *)
    fun checkcons (ctx as C { tpcons, ...}) p1 p2 =
        (* hacky special case *)
        case p1 of
            IL.PConst "bot" => true
          | _ =>
            let val (p1, p2) = (ground p1, ground p2)
            in
                if IL.pr_eq (p1, p2) then
                    true
                else if tpc_mem tpcons (p1, p2) then
                    true
                else
                    let val gs = get_greater tpcons p1
                    in
                        List.exists (fn p => checkcons ctx p p2) gs
                    end
            end

    fun bindpcons (ctx as C { cons, vars, dbs, mobiles, pcons, tpcons, plabs, sign })
                  (p1, p2) =
        if checkcons ctx p2 p1 then
            raise (Context "cyclic ordering constraint introduced!")
        else
            C { cons = cons,
                vars = vars,
                mobiles = mobiles,
                pcons = (p1, p2)::pcons,
                tpcons = (tpc_insert tpcons (p1, p2)),
                plabs = plabs,
                dbs = dbs,
                sign = sign
              }

    fun bindsig (C { cons, vars, dbs, mobiles, pcons, tpcons, plabs, sign }) s con = 
        C { vars = vars,
            cons = cons,
            mobiles = mobiles, 
            pcons = pcons,
            tpcons = tpcons,
            plabs = plabs,
            dbs = dbs,
            sign = S.insert (sign, s, con)}

    fun bindpath c longid t v = 
        case longid of 
            IL.Id i => bindv c i t v
          | IL.Path (i, p) => let val newcon = bindpath c p t v
                             in bindsig c i newcon
                             end 

    fun pathex (C {sign, ...}) sym =
        (case S.find (sign, sym) of
             SOME x => x
           | NONE => absent "sign" sym)

    fun plabs (C { plabs, ... }) = SSU.tolist plabs
    fun pcons (C { pcons, ... }) = pcons

    val empty = C { vars = S.empty, 
                    cons = S.empty, 
                    mobiles = VS.empty,
                    plabs = SS.empty,
                    pcons = [],
                    tpcons = tpc_empty,
                    dbs = S.empty, 
                    sign = S.empty }





    (* check if priorities in s1 is less than priorities in s2 *)
    fun check_cons ctx (s1, s2) = 
      IL.PrioSet.foldr 
        (fn (p, b) => 
          (IL.PrioSet.foldr (fn (p', b') => 
            (checkcons ctx p' p) andalso b') true s1) andalso b) 
        true
        s2

    (* check solutions satifying all psconstraints *)
    fun check_pscstrs_sol (ctx: context) 
                          (psctx: pscontext) 
                          (pscstrs: psconstraint list) = 
      let 
        fun error_msg (ps1, s1) (ps2, s2) = 
           Layout.tostring (ILPrint.pstol ps1)
           ^ " (" ^ Layout.tostring (ILPrint.pstol (IL.PSSet s1)) ^ ") and "
           ^ Layout.tostring (ILPrint.pstol ps2)
           ^ " (" ^ Layout.tostring (ILPrint.pstol (IL.PSSet s2)) ^ ")"

        (* get set solution in priority set context *)
        fun get_set ps = 
          (case ps of 
             IL.PSSet s => s
           | IL.PSEvar e => 
              (case (PSEvarMap.find (psctx, IL.PSEvar e)) of
                SOME s => s
              | _ => raise (PSConstraints "cannot find psevar in context")))

        (*
          (* check if solved system has empty solution *)
          fun check_empty psctx = 
            if List.all (fn ps => not (IL.PrioSet.isEmpty ps)) (PSEvarMap.listItems psctx) then ()
            else raise (PSConstraints "empty priority set")
        *)

        (* helper function to check set constraint *)
        fun check (IL.PSSup (ps1, ps2)) = 
            let val s1 = get_set ps1
                val s2 = get_set ps2
            in
              (if check_sup (s1, s2) then ()
               else raise 
                  (PSConstraints 
                    ("superset violated: " 
                     ^ (error_msg (ps1, s1) (ps2, s2)))))
            end
          | check (IL.PSCons (ps1, ps2)) =
            let val s1 = get_set ps1
                val s2 = get_set ps2
            in
              (if check_cons ctx (s1, s2) then ()
               else raise 
                  (PSConstraints 
                    ("priority set constraint violated: "
                     ^ (error_msg (ps1, s1) (ps2, s2)))))
            end
      in 
        List.app check pscstrs 
      end

end
