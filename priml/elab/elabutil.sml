
structure ElabUtil :> ELABUTIL =
struct

    exception Elaborate of string
    structure V = Variable
    structure PSC = PSContext

    infixr 9 `
    fun a ` b = a b

    val ltos = Pos.toString

    fun snd (x, y) = y

    fun error loc msg =
        let in
            print ("Error at " ^ Pos.toString loc ^ ": ");
            print msg;
            print "\n";
            raise Elaborate "error"
        end

    val all_evars  = ref (nil : IL.typ IL.ebind ref list)
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
      let val e = Unify.new_ebind ()
      in
        all_evars := e :: !all_evars;
        IL.Evar e
      end
    fun new_pevar () =
      let val e = Unify.new_ebind ()
      in
        all_wevars := e :: !all_wevars;
        IL.PEvar e
      end
    fun new_psevar () = 
      let val e = Unify.new_ebind ()
      in
        all_psevars := e :: !all_psevars;
        IL.PSEvar e
      end

    (* XXX5 compile flag *)
    fun warn loc s =
      let in
        print ("Warning at " ^ Pos.toString loc ^ ": " ^ s ^ "\n")
      end

    fun psubst1 w v t = Subst.prsubst ((Subst.fromlist [(v,w)]) : Subst.prio Subst.subst) t
    fun psubsc1 w v c =
        ((* print ("subbing for " ^ (Variable.show v) ^ "\n"); *)
         Subst.prsubsc ((Subst.fromlist [(v,w)]) : Subst.prio Subst.subst) c)

    (* rename psevar in priority set *)
    fun psesubps psemap ps =  
      case ps of 
        IL.PSSet _ => (psemap, ps)
      | IL.PSEvar _ =>
          (case PSC.PSEvarMap.find (psemap, ps) of
              NONE => 
                let val ps' = new_psevar ()
                    val psemap' = PSC.PSEvarMap.insert (psemap, ps, ps') 
                in  
                  (psemap', ps')
                end
            | SOME ps' => (psemap, ps'))

    (* rename psevars in list of psconstraints *)
    fun psesubspscs psemap pscons =
      let 
        (* rename psevars in psconstraint *)
        fun psesubspsc (pscon, (psemap, pscons)) =
          case pscon of
               IL.PSCons (ps1, ps2) =>
                let val (psemap', ps1') = psesubps psemap ps1
                    val (psemap'', ps2') = psesubps psemap' ps2
                 in 
                   (psemap'', pscons @ [IL.PSCons (ps1', ps2')])
                 end
             | IL.PSSup (ps1, ps2) =>
                let val (psemap', ps1') = psesubps psemap ps1
                    val (psemap'', ps2') = psesubps psemap' ps2
                 in 
                   (psemap'', pscons @ [IL.PSSup (ps1', ps2')])
                 end
      in
        List.foldl psesubspsc (psemap, []) pscons
      end

    (* make a copy and rename psevars in psconstrraints in type *)
    fun psesubst t = 
        let 
          fun psesubst_rec psemap t = 
            case t of 
                 IL.TCmd (t', (pr1, pr2, pr3), pscons) => 
                    let val (psemap', pscons') = psesubspscs psemap (!pscons)
                        val (psemap', pr1') = psesubps psemap' pr1
                        val (psemap', pr2') = psesubps psemap' pr2
                        val (psemap', pr3') = psesubps psemap' pr3
                        val (psemap', t'') = psesubst_rec psemap' t'
                    in
                      (psemap', IL.TCmd (t'', (pr1', pr2', pr3'), ref pscons'))
                    end
               | IL.TForall (vl, cons, t') => 
                   let val (psemap', t'') = psesubst_rec psemap t' 
                   in
                     (psemap', IL.TForall (vl, cons, t''))
                   end
               | IL.TThread (t', ps, pscons) => 
                   let val (psemap', pscons') = psesubspscs psemap (!pscons)
                       val (psemap', t'') = psesubst_rec psemap' t' 
                   in
                     (psemap', IL.TThread (t'', ps, ref pscons'))
                   end
               | IL.Arrow (r, tl, t') => 
                   let val (psemap', t'') = psesubst_rec psemap t' 
                       val (psemap', tl') = List.foldl (fn (t, (psemap, tl)) =>
                                                          let val (psemap', t') = psesubst_rec psemap t
                                                          in (psemap', tl @ [t'])
                                                          end)
                                                       (psemap, [])
                                                       tl
                   in
                     (psemap', IL.Arrow (r, tl', t''))
                   end
               | IL.TVec t' => 
                   let val (psemap', t'') = psesubst_rec psemap t' 
                   in
                     (psemap', IL.TVec t'')
                   end
               | IL.TCont t' => 
                   let val (psemap', t'') = psesubst_rec psemap t' 
                   in
                     (psemap', IL.TCont t'')
                   end
               | IL.TTag (t', v) => 
                   let val (psemap', t'') = psesubst_rec psemap t' 
                   in
                     (psemap', IL.TTag (t'', v))
                   end
               | IL.TRec stl =>
                   let val (psemap', stl') = List.foldl (fn ((l, t), (psemap, stl)) => 
                                                            let val (psemap', t') = psesubst_rec psemap t
                                                            in (psemap', stl @ [(l, t')])
                                                            end)
                                                        (psemap, [])
                                                        stl
                   in
                     (psemap', IL.TRec stl')
                   end
               | IL.Sum lcl =>
                   let val (psemap', lcl') = 
                      List.foldl (fn ((l, tarm), (psemap, lcl)) => 
                                    case tarm of 
                                         IL.NonCarrier => (psemap, lcl @ [(l, tarm)])
                                       | IL.Carrier { definitely_allocated, carried } =>
                                           let val (psemap', t') = psesubst_rec psemap carried
                                               val tarm' = IL.Carrier { definitely_allocated=definitely_allocated, 
                                                                     carried = t' }
                                           in (psemap', lcl @ [(l, tarm')])
                                           end)
                                  (psemap, [])
                                  lcl
                   in
                     (psemap', IL.Sum lcl')
                   end
               | IL.Mu (i, m) =>
                   let val (psemap', m') = List.foldl (fn ((v, t), (psemap, m)) => 
                                                          let val (psemap', t') = psesubst_rec psemap t
                                                          in (psemap', m @ [(v, t')])
                                                          end)
                                                      (psemap, [])
                                                      m
                   in
                     (psemap', IL.Mu (i, m'))
                   end
               | IL.Evar (ref (IL.Bound t')) =>
                   let val (psemap', t'') = psesubst_rec psemap t'
                   in
                     (psemap', IL.Evar (ref (IL.Bound t'')))
                   end
               | _ => (psemap, t)
        in
          snd (psesubst_rec (PSC.PSEvarMap.empty) t)
        end

    (* unify context location message actual expected *)
    fun unify ctx loc msg t1 t2 =
            Unify.unify ctx t1 t2
            handle Unify.Unify s => 
                let 
                    val $ = Layout.str
                    val % = Layout.mayAlign
                in
                    Layout.print
                    (Layout.align
                     [%[%[$("Type mismatch (" ^ s ^ ") at "), %[$(Pos.toString loc),
                          $": "], $msg]],
                      %[$"expected:", Layout.indent 4 (ILPrint.ttolex (MuName.name ctx) t2)],
                      %[$"actual:  ", Layout.indent 4 (ILPrint.ttolex (MuName.name ctx) t1)]],
                     print);
                    print "\n";
                    raise Elaborate "type error"
                end

    (* unify context location message actual expected *)
    fun unifyp ctx loc msg w1 w2 =
            Unify.unifyp ctx w1 w2
            handle Unify.Unify s => 
                let 
                    val $ = Layout.str
                    val % = Layout.mayAlign
                in
                    Layout.print
                    (Layout.align
                     [%[$("World mismatch (" ^ s ^ ") at "), $(Pos.toString loc),
                        $": ", $msg],
                      %[$"expected:", Layout.indent 4 (ILPrint.prtol w2)],
                      %[$"actual:  ", Layout.indent 4 (ILPrint.prtol w1)]],
                     print);
                    print "\n";
                    raise Elaborate "type error"
                end


    fun check_constraint ctx loc p1 p2 =
        if Context.checkcons ctx p1 p2 then
            ()
        else
            let 
                val $ = Layout.str
                val % = Layout.mayAlign
            in
                Layout.print
                    (Layout.align
                         [%[$"constraint violated at ", $(Pos.toString loc), $": ",
                            (ILPrint.prtol p1), $" <= ", (ILPrint.prtol p2)]],
                     print);
                print "\n";
                raise (Elaborate "constraint violated ")
            end


    local open Primop Podata
    in
      fun ptoil PT_INT = Initial.ilint
        | ptoil PT_STRING = Initial.ilstring
        | ptoil PT_BOOL = Initial.ilbool
        | ptoil (PT_VAR v) = IL.TVar v
        | ptoil (PT_REF p) = IL.TRef ` ptoil p
        | ptoil (PT_ARRAY p) = IL.TVec ` ptoil p
        | ptoil PT_UNIT = IL.TRec nil
        | ptoil PT_CHAR = Initial.ilchar
        | ptoil PT_UNITCONT = raise Elaborate "unimplemented potoil unitcont"
    end

(*
    local open JSImports
    in
      fun jtoil G JS_EVENT = 
        (case Context.con G Initial.eventname of
           (0, IL.Typ t, IL.Regular) => t
         | _ => raise Elaborate "event is wrongly declared??")
        | jtoil G JS_CHAR = Initial.ilchar
    end
*)

    val itos = Int.toString

    val newstr = ML5pghUtil.newstr

    (* This uses the outer context to figure out which evariables can be generalized. *)
    fun polygen ctx (ty : IL.typ) (* (atworld : IL.prio) *) =
        let 
            val acct = ref nil
            val accw = ref nil

(*
            val occurs_in_atworld =
              (* path compress first *)
              let 
                fun mkfun w =
                  case w of
                    IL.PEvar er =>
                      (case !er of
                         IL.Bound ww => mkfun ww
                       | IL.Free m => (fn n => n = m))
                  | _ => (fn _ => false)
              in
                mkfun atworld
              end

            fun gow w =
              (case w of
                 IL.PEvar er =>
                   (case !er of
                      IL.Bound ww => gow ww
                    | IL.Free n => 
                        if Context.has_wevar ctx n orelse occurs_in_atworld n
                        then w
                        else
                          let val wv = V.namedvar "wpoly"
                          in
                            accw := wv :: !accw;
                            er := IL.Bound (IL.PVar wv);
                            IL.PVar wv
                          end)
               | IL.PVar _ => w
               | IL.PConst _ => w)
*)

            fun got t =
                (case t of
                     IL.TRef tt => IL.TRef ` got tt
                   | IL.TVec tt => IL.TVec ` got tt
                   | IL.Sum ltl => IL.Sum ` ListUtil.mapsecond (IL.arminfo_map got) ltl
                   | IL.Arrow (b, tl, tt) => IL.Arrow(b, map got tl, got tt)
                   | IL.Arrows al => IL.Arrows ` map (fn (b, tl, tt) => 
                                                      (b, map got tl, got tt)) al
                   | IL.TRec ltl => IL.TRec ` ListUtil.mapsecond got ltl
                   | IL.TVar v => t
                   | IL.TCont tt => IL.TCont ` got tt
                   | IL.TTag (tt, v) => IL.TTag (got tt, v)
                   | IL.Mu (n, vtl) => IL.Mu (n, ListUtil.mapsecond got vtl)
(*
                   | IL.TAddr w => IL.TAddr (gow w)
                   | IL.Shamrock (w, tt) => IL.Shamrock (w, got tt)
                   | IL.At (t, w) => IL.At(got t, gow w)
*)
                   | IL.TCmd (t, p, c) => IL.TCmd (got t, p, c)
                   | IL.TThread (t, p, c) => IL.TThread (got t, p, c)
                   | IL.TForall (v, c, t) => IL.TForall (v, c, got t)
                   | IL.Evar er =>
                         (case !er of
                              IL.Free n =>
                                  if Context.has_evar ctx n
                                  then t
                                  else
                                      let 
                                          val tv = V.namedvar (Nonce.nonce ())
                                      in
                                          acct := tv :: !acct;
                                          er := IL.Bound (IL.TVar tv);
                                          IL.TVar tv
                                      end
                            | IL.Bound ty => got ty))
        in
            { t = got ty, tl = rev (!acct), wl = rev (!accw) }
        end

    fun polywgen ctx (w as IL.PEvar er) =
      (case !er of
         IL.Free n =>
           if Context.has_wevar ctx n
           then
             let in
               (* print "no polywgen: occurs\n"; *)
               NONE
             end
           else
               let
                   val wv = V.namedvar (Nonce.nonce ()) (* "polyw" *)
               in
                   er := IL.Bound (IL.PVar wv);
                   (* print "yes polywgen\n"; *)
                   SOME wv
               end
       | IL.Bound w => polywgen ctx w)
      | polywgen ctx (w as IL.PConst s) = 
         let in
           (* print "no polywgen: const\n"; *)
           NONE
         end
      | polywgen _   (w as IL.PVar v) = 
         let in
           print ("no polywgen: var " ^ V.tostring v ^ "\n");
           NONE
         end

    fun evarizes (IL.Poly({prios, tys}, mt)) =
        let
          (* make the type and world substitutions *)
            fun mkts nil m ts = (m, rev ts)
              | mkts (tv::rest) m ts =
              let val e = new_evar ()
              in
                mkts rest (V.Map.insert (m, tv, e)) (e :: ts)
              end

            fun mkws nil m ws = (m, rev ws)
              | mkws (tv::rest) m ws =
              let val e = new_pevar ()
              in
                mkws rest (V.Map.insert (m, tv, e)) (e :: ws)
              end

            val (wsubst, ws) = mkws prios V.Map.empty nil
            val (tsubst, ts) = mkts tys V.Map.empty nil

            fun wsu t = Subst.prsubst wsubst t
            fun tsu t = Subst.tsubst tsubst t

        in
          (map ((* wsu o *) tsu) mt, ws, ts)
        end

    fun evarize (IL.Poly({prios, tys}, mt)) = 
      case evarizes ` IL.Poly({prios=prios, tys=tys}, [mt]) of
        ([m], ws, ts) => (m, ws, ts)
      | _ => raise Elaborate "impossible"


  (* used to deconstruct bool, which the compiler needs internally.
     implemented for general purpose (except evars?) *)
  fun unroll loc (IL.Mu(m, tl)) =
      (let val (_, t) = List.nth (tl, m)
           val (s, _) =
               List.foldl (fn((v,t),(mm,idx)) =>
                           (V.Map.insert
                            (mm, v, (IL.Mu (idx, tl))), idx + 1))
                          (V.Map.empty, 0)
                          tl
       in
           Subst.tsubst s t
       end handle _ => error loc "internal error: malformed mu")
    | unroll loc _ =
      error loc "internal error: unroll non-mu"

  fun mono t = IL.Poly({prios= nil, tys = nil}, t)
(*
  local
    val mobiles = ref nil : (Context.context * Pos.pos * string * IL.typ) list ref

    (* Like Context.has_evar; if we have decided that an evar must be mobile,
       then we can't generalize it because we don't have bounded quantification
       over mobile types. *)
    fun mobiles_have_evar n =
        List.exists (fn (G, _, _, t) =>
                     raise Fail "XXX FIXME HERE"
                     ) (!mobiles)

    (* mobility test.
       if force is true, then unset evars are set to unit
       to force mobility.
       if force is false and evars are seen, then defer this type for later *)
                    
    fun emobile G pos s force t =
      let

        (* argument: set of mobile type variables *)
        fun em G t =
          case t of
            IL.Evar (ref (IL.Bound t)) => em G t
          | IL.Evar (ev as ref (IL.Free _)) => 
              if force
              then 
                let in
                  warn pos (s ^ ": unset evar in mobile check; setting to unit");
                  ev := IL.Bound (IL.TRec nil);
                  true
                end
              else (mobiles := (G, pos, s, t) :: !mobiles; true)

          | IL.TVar v => Context.ismobile G v

          | IL.TRec ltl => ListUtil.allsecond (em G) ltl
          | IL.Arrow _ => false
          | IL.Arrows _ => false
          | IL.Sum ltl => List.all (fn (_, IL.NonCarrier) => true 
                                     | (_, IL.Carrier { carried = t, ...}) => em G t) ltl

          (* no matter which projection this is, all types have to be mobile *)
          | IL.Mu (i, vtl) => 
              let val G = foldr (fn (v, G) => Context.bindmobile G v) G ` map #1 vtl
              in ListUtil.allsecond (em G) vtl
              end

          (* assuming immutable. 
             there should be a separate array type *)
          | IL.TVec t => em G t
          (* continuations aren't mobile. They could do anything. *)
          | IL.TCont t => false
          | IL.TRef _ => false
          (* the representation of a tag is always portable, but the 
             tag type is only mobile if its body is mobile. This is
             because a tag is permission to possibly use an extensible
             type at that type. *)
          | IL.TTag (t, _) => em G t
          | IL.At _ => true
          | IL.TAddr _ => true
          | IL.Shamrock _ => true
      in
        em G t
      end


    fun notmobile ctx loc msg t =
      let 
        val $ = Layout.str
        val % = Layout.mayAlign
      in
        Layout.print
        (Layout.align
         [%[$("Error: Type is not mobile at "), $(Pos.toString loc),
            $": ", $msg],
          %[$"type:  ", Layout.indent 4 (ILPrint.ttolex (MuName.name ctx) t)]],
         print);
        print "\n";
        raise Elaborate "type error"
      end

  in
    fun clear_mobile () = mobiles := nil

    fun check_mobile () =
      let in
        List.app (fn (ctx, pos, msg, t) => 
                  if emobile ctx pos msg true t
                  then () 
                  else notmobile Context.empty pos msg t) (!mobiles);
        clear_mobile ()
      end
 
    fun require_mobile ctx loc msg t =
        if emobile ctx loc msg false t
        then ()
        else notmobile ctx loc msg t

  end
*)

end
