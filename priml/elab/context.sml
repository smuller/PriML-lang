
structure Context :> CONTEXT =
struct
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

    type tpcons = SS.set S.map

    val tpc_empty =
        S.empty

    fun ground (IL.PEvar r) =
        (case !r of
             IL.Free _ => raise (Context "prio not constant or variable")
           | IL.Bound x => x)
      | ground p = p

    fun s_of_p (IL.PConst c) = c
      | s_of_p (IL.PVar v) = (Variable.show v)
      | s_of_p _ = raise (Context "prio cons not constant or variable")

    fun tpc_insert m (p1, p2) =
	let 
	    val s1 = s_of_p p1
	    val s2 = s_of_p p2
	in
	    case S.find (m, s1) of
		SOME ss => (S.insert (m, s1, SS.add (ss, s2)))
	      | NONE => S.insert (m, s1, SS.singleton s2)
	end

    fun tpc_mem (m: tpcons) (p1, p2) =
	let 
	    val s1 = s_of_p p1
	    val s2 = s_of_p p2
	in
            case S.find (m, s1) of
		SOME ss => SS.member (ss, s2)
              | NONE => false
	end

    fun get_greater m p =
	let val s = s_of_p p
	in
	    case S.find (m, s) of
		SOME ss => (List.map IL.PConst (SSU.tolist ss))
              | NONE => []
	end

    datatype context = 
        (* prios = priority variables *)
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
        %[$"Context.",
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
                       List.exists (fn (_, t) => has t) tl
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
                                       has t orelse
				       List.exists (fn (_, t) => has t) tl) l
                 | TRef t => has t
                 | TCmd (t, _) => has t
                 | TThread (t, _) => has t
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
                       List.exists (fn (_, t) => has t) tl
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
                                       has t orelse
				       List.exists (fn (_, t) => has t) tl) l
                 | TRef t => has t
                 | TCmd (t, _) => has t
                 | TThread (t, _) => has t
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

    fun rem (C {vars, cons, dbs, plabs, pcons, tpcons, mobiles, sign }) sym =
	(let val (vars', r) = S.remove (vars, sym)
	     val ctx = C {vars=vars', cons=cons, dbs=dbs, plabs=plabs, pcons=pcons, tpcons=tpcons, mobiles=mobiles, sign=sign }
	 in
	     SOME (ctx, r)
	 end)
	handle _ => NONE
		      
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
      let 
        val sym = (case sym of NONE => 
                     ML5pghUtil.newstr "bindex" | SOME s => s)
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
                             (typ, var, stat)),
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

end
