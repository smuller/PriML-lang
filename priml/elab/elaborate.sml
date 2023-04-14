
structure Elaborate :> ELABORATE =
struct

  val sequenceunit = Params.flag false
    (SOME ("-sequence-unit", 
           "Require sequenced expressions and 'do' declarations to be of type unit")) "sequenceunit"

  val warnmatch = Params.flag true
    (SOME ("-warn-match",
           "(Conservative) warnings for non-exhaustive matches")) "warnmatch"

  infixr 9 `
  fun a ` b = a b
  fun I x = x

  structure V = Variable
  structure C = Context
  structure E = EL

  open IL
  open ElabUtil
  open PSetCstrs
  structure P = Primop

  exception Impossible

  fun bindval p = Val p

  fun printp p = Layout.print (ILPrint.prtol p, print)
    
  fun printps ps = Layout.print (ILPrint.pstol ps, print)

  fun printe e = Layout.print (ILPrint.etol e, print)

  fun printc c = Layout.print (ILPrint.ctol c, print)

  val _ = C.install_ne new_evar

  (* XXX elabutil *)
  fun mkfn (args, dom, cod, body) =
      let val f = V.namedvar "fn"
          val unused = V.namedvar "nonrec"
      in
        FSel(0,
             Fns [{ name = unused,
                    arg = args,
                    dom = dom,
                    cod = cod,
                    inline = false,
                    total = false,
                    (* since the name is new, it cannot be recursive *)
                    recu = false,
                    body = body }])
      end

  (* ditto *)
  fun tuple l =
      let
          fun mktup _ nil = nil
            | mktup n (h::t) = 
              (Int.toString n, h) :: 
              mktup (n + 1) t
      in
          IL.TRec(mktup 1 l)
      end

  fun lookupt ctx loc str =
      (case C.con ctx str of
           (0, Typ t, _) => t
         (* nullary rewrites these, so it should be impossible *)
         | (0, Lambda f, _) => error loc ("invariant violation: lookupt got Lambda for " ^ str)
         | (kind, _, _) => 
               error loc (str ^ " expects " ^ 
                          itos kind ^ " type argument"
                          ^ (if kind = 1 then "" else "s") ^ "."))
           handle C.Absent _ => error loc ("Unbound type name " ^ str)

  and elabpr ctx loc w =
    (C.prio ctx w)
    handle C.Absent _ => error loc ("Unbound priority variable/constant " ^ w)

  and elabt ctx loc t = elabtex ctx NONE loc t

  (* XXX no need for prefix any more *)
  and elabtex ctx prefix loc t =
      (case t of
         E.TVar str => lookupt ctx loc str
       | E.TApp (l, str) =>
             (* XXX there are no modvars any more *)
             ((case C.con ctx str of
                   (kind, Lambda f, _) =>
                       if kind = length l 
                       then f (map (elabtex ctx prefix loc) l) 
                       else error loc 
                           (str ^ " expects " ^ itos kind ^ " type argument"
                            ^ (if kind = 1 then "" else "s") ^ " -- gave " ^
                            itos (length l))
                 | _ => error loc (str ^ " is not a type constructor."))
                   handle Context.Absent _ => 
                          error loc ("Unbound type constructor " ^ str))
(*
       | E.TAddr w => TAddr (elabw ctx loc w)
       | E.TAt (t, w) => At (elabtex ctx prefix loc t, elabw ctx loc w)
       (* XXX5 allow world var *)
       | E.TSham (NONE, t) => Shamrock(V.namedvar "shamt_unused", elabtex ctx prefix loc t)
       | E.TSham (SOME _, _) => error loc "sham vars unimplemented (and how did you get one??)"
*)
       | E.TRec ltl => let 
                           val ltl = ListUtil.sort 
                                     (ListUtil.byfirst ML5pghUtil.labelcompare) ltl
                       in 
                           if ListUtil.alladjacent
                                (ListUtil.byfirst op<>) ltl 
                           then TRec (ListUtil.mapsecond (elabtex ctx prefix loc) ltl)
                           else error loc "Duplicate label in record type"
                       end
       | E.TNum n => if n >= 0
                     then 
                       TRec (List.tabulate(n, (fn i => (Int.toString (i + 1),
                                                        new_evar ()))))
                     else error loc "num type (record length) must be non-negative"
       | E.TArrow (dom, cod) => Arrow (false,
                                       [elabtex ctx prefix loc dom],
                                       elabtex ctx prefix loc cod)
       | E.TCmd (t, p) => 
           let val ps = PSSet (PrioSet.singleton (elabpr ctx loc p))
           in 
             TCmd (elabtex ctx prefix loc t, (ps, new_psevar (), new_psevar ()))
           end
       | E.TThread (t, p) => TThread (elabtex ctx prefix loc t, PSSet (PrioSet.singleton (elabpr ctx loc p)))
       | E.TForall (E.PPVar s, t) =>
         let val v = V.namedvar s
         in
             TForall ([v], [], elabtex (C.bindp ctx s v) prefix loc t)
         end
       | E.TForall (E.PPConstrain (s, cs), t) =>
         let val v = V.namedvar s
             val cs = List.map (fn (p1, p2) => PCons (elabpr ctx loc p1,
                                                      elabpr ctx loc p2))
                               cs
         in
             TForall ([v], cs, elabtex (C.bindp ctx s v) prefix loc t)
         end)

    and dovar ctx loc vv =
    ((case C.var ctx vv of
      (pt, v, i) =>
        let
            (* See below *)
            (* val _ = print "evarizing\n" *)
            val (tt, prios, tys) = evarize pt
            (* val _ = print "done evarizing\n" *)
        in
          (*
          print ("use uvar " ^ vv ^ " : ");
          Layout.print(ILPrint.ttol tt, print);
          print " @ ";
          Layout.print(ILPrint.wtol here, print);
          print "\n";
          *)
          (Polyuvar {tys = tys, prios = prios, var = v}, tt)
        end
            (*
    | (pt, v, i, Context.Modal w) =>
        let
            (* If polymorphic, instantiate the variable's 
               forall-quantified type variables with new 
               evars. Use type application on the expression 
               to record this. *)

            val (tt, worlds, tys) = evarize pt
        in
            (Polyvar {tys = tys, worlds = worlds, var = v}, tt, w)
        end) *)) handle C.Absent _ =>
                  error loc ("Unbound identifier: " ^ vv)
    )


  and dopath ctx loc path = 
    (case path of 
        (E.Id id) => dovar ctx loc id
      | (E.Path (i, p)) => dopath (C.pathex ctx i) loc p
    ) handle C.Absent _ => error loc ("Unbound identifier: " (* insert pretty printer here *))

  and value (v, t) = (Value v, t)

  and elab ctx ((e, loc) : EL.exp) =
      case e of
          E.Seq (e1, e2) => 
              let val (e1, e1t) = elab ctx e1
                  val (e2, e2t) = elab ctx e2
              in 
                (if !sequenceunit
                 then unify ctx loc "sequence unit" e1t (IL.TRec nil)
                 else ());
                (Seq(e1, e2), e2t)
              end

        | E.Var vv => 
              let 
                val (v, t) = dopath ctx loc vv
              in
(*                 unifyw ctx loc ("variable " ^ vv) here w; *)
                value (v, t)
              end

(*
        | E.Get(addr, body) =>
              let
                val (aa, at) = elab ctx here addr
                val there = new_wevar ()
                val () = unify ctx loc "get addr" at (IL.TAddr there)
                val (bb, bt) = elab ctx there body
              in
                require_mobile ctx loc "get" bt;
                print "in get: here = ";
                Layout.print(ILPrint.wtol here, print);
                print " and there = ";
                Layout.print(ILPrint.wtol there, print);
                print "\n";
                (Get { addr = aa, typ = bt, body = bb, dest = there }, bt)
              end
*)

        | E.Primapp (p, ts, es) =>
              (case Primop.fromstring p of
                 NONE => error loc ("unknown primitive in primapp: " ^ p)
               | SOME po =>
                   let
                     val { worlds, tys, dom, cod } = Podata.potype po
                     val dom = map ptoil dom
                     val cod = ptoil cod
                     
                   in
                     if List.null worlds
                     then if length tys = length ts
                        then if length es = length dom
                             then
                               let
                                 val ts = map (elabt ctx loc) ts
                                 val (args, argts) = ListPair.unzip ` map (elab ctx) es
                                   
                                 val (l, _, tvs) = ElabUtil.evarizes (Poly({prios=nil,
                                                                            tys=tys},
                                                                           cod :: dom))
                                   
                                 val cod = hd l
                                 val dom = tl l
                                   
                               in
                                 (* One side is all unique evars, so this always succeeds *)
                                 ListPair.app (fn (t1, t2) =>
                                               unify ctx loc "primapp" t1 t2) (tvs, ts);
                            
                                 (* args must match domain *)
                                 ListPair.app (fn (t1, t2) =>
                                          unify ctx loc "primapp arg" t1 t2) (dom, argts);
                                 
                                 (Primapp(po, args, ts),
                                  cod)
                               end
                             else error loc "not the right number of val args in primapp"
                        else error loc "not the right number of type args in primapp"
                     else error loc "unimplemented: world polymorphism in primop"
                   end)
                   

        | E.Constant(E.CInt i) => value (Int i, Initial.ilint)
        | E.Constant(E.CChar c) => value (Int (Word32.fromInt (ord c)), Initial.ilchar)

        | E.Float _ => error loc "unimplemented: floating point"

        | E.Constant (E.CString s) => value (String s, Initial.ilstring)

        | E.Vector nil => 
              let
                val t = new_evar()
              in
                (Primapp(P.PArray0, nil, [t]), TVec t)
              end

        (* XXX this is probably not good enough since it should be a value *)
        (* derived form *)
        | E.Vector (first::rest) =>
               let
                   (* [| x, y, z |]

                      becomes

                      let val a = array (3, x)
                      in
                          update(array, 1, y);
                          update(array, 2, z);
                          a
                      end *)

                   fun $x = (x, loc)
                   val n = 0w1 + Word32.fromInt (length rest)
                   val arr = newstr "arr"

                   fun dowrites _ nil e = e
                     | dowrites m (h::t) e =
                       $ ` 
                       E.Seq
                       ($ `
                        E.App($ ` E.Var (E.Id "update_"),
                              $ ` 
                              E.Record
                              [("1", $ ` E.Var (E.Id arr)),
                               ("2", $ ` E.Constant ` E.CInt m),
                               ("3", h)],
                             false),
                        dowrites (m + 0w1) t e)
               in
                   elab ctx `
                   $ `
                    E.Let
                    ($ `
                     E.Val (nil, E.PVar arr,
                             $ `
                             E.App ($ ` E.Var (E.Id "array"),
                                    $ `
                                    E.Record
                                    [("1", $ ` E.Constant ` E.CInt n),
                                     ("2", first)],
                                    false)),
                     dowrites 0w1 rest ` $ ` E.Var (E.Id arr))
               end

(*
        | E.Say (imps, ee) => 
               let
                 fun sayimport s = jtoil ctx (case JSImports.importtype s of
                                                NONE => error loc ("unknown say import " ^ s)
                                              | SOME j => j)

                 val out = V.namedvar "say_out"
                 val k   = V.namedvar "say_k"

                 val imps = map (fn (imp, s) => (imp, s, V.namedvar s, sayimport imp)) imps
                 (* bind the imports *)
                 val ctx = foldr (fn ((imp, s, v, t), ctx) =>
                                  C.bindv ctx s (mono t) v here) ctx imps

                 val tuple  = V.namedvar "say_tuple"
                 val tuplet = TRec ` ListUtil.mapi (fn ((_, _, _, t), i) => (Int.toString (i + 1), t)) imps

                 val (ee, tt) = elab ctx here ee

                 fun project _ nil e = e
                   | project n ((imp, s, v, t) :: rest) e =
                   Let(Bind(Val, mono (v, t, Proj(Int.toString n, tuplet, Value ` Var tuple))),
                       project (n + 1) rest e)

               in
                 (* expression must have type unit *)
                 unify ctx loc "say" tt (IL.TRec nil);
                 (* we must be home. perhaps this restriction
                    could be relaxed so that only 'exp' is home,
                    but I am not sure of the consequences and
                    I think that would be pretty useless *)
                 unifyw ctx loc "say" here Initial.home;

                 (* then we generate:
                   letcc out : string cont
                   in 
                      let (v1, v2, ...) = 
                         letcc k : tuplet cont
                         in throw (say (imports, k)) to out
                         end
                      in
                         ( k continuation starts execution here )
                         let val s = [hello]
                         in alert s
                         end;
                         halt
                      end
                   end
                 *)
                 (Letcc (out, Initial.ilstring,
                         Let(Bind(Val,
                                  mono
                                  (tuple,
                                   tuplet,
                                   (Letcc(k, tuplet,
                                          Throw (Say (map (fn (imp, _, _, t) => (imp, t)) imps, Value ` Var k), 
                                                 Value ` Var out))))),
                             (* project components *)
                             project 1 imps `
                             (* then do the expression *)
                             Seq(ee,
                                 (* and halt at string type *)
                                 Primapp(Primop.PHalt, [], [Initial.ilstring])
                                 ))),
                  Initial.ilstring)
               end

        | E.Throw (e1, e2) => 
               let
                 val (ee1, t1) = elab ctx here e1
                 val (ee2, t2) = elab ctx here e2
               in
                 (* thrown expression must equal cont type *)
                 unify ctx loc "throw" t2 (IL.TCont t1);
                 (Throw(ee1, ee2), new_evar ())
               end

        | E.Letcc (s, e) =>
               let
                 val cv = V.namedvar s
                 val bodt = new_evar ()
                 val ctx' = C.bindv ctx s (mono (IL.TCont bodt)) cv here
                   
                 val (ee, tt) = elab ctx' here e
               in
                 unify ctx loc "letcc" tt bodt;
                 (Letcc (cv, bodt, ee), bodt)
               end
               
        (* better code for string constants *)
        | E.Jointext [e] => 
               let val (e, t) = elab ctx here e
               in  unify ctx loc "jointext-singleton" t Initial.ilstring;
                   (e, t)
               end

        | E.Jointext el =>
               let
                   val (ees, tts) = ListPair.unzip (map (elab ctx here) el)
               in
                   app (fn t => unify ctx loc "jointext" t Initial.ilstring) tts;

                   (Primapp(Primop.PJointext (length ees), ees, nil), Initial.ilstring)
               end

*)

        | E.Record lel =>
               let
                   val letl = ListUtil.mapsecond (elab ctx) lel
                   val _ = ListUtil.alladjacent (ListUtil.byfirst op<>) 
                              (ListUtil.sort 
                               (ListUtil.byfirst ML5pghUtil.labelcompare) lel)
                           orelse error loc 
                              "Duplicate labels in record expression"
               in
                   (* might be a value, if everything is a value *)
                 if List.all (fn (_, (Value _, _)) => true | _ => false) letl
                 then
                     (Value ` VRecord (map (fn (l, (Value e, t)) => (l, e) 
                                            | _ => error loc "impossible") letl),
                      TRec (map (fn (l, (e, t)) => (l, t)) letl))
                 else
                     (Record (map (fn (l, (e, t)) => (l, e)) letl),
                      TRec (map (fn (l, (e, t)) => (l, t)) letl))
               end

        | E.Proj (s, t, e) =>
               let
                   val (ee, tt) = elab ctx e
                   val ttt = elabt ctx loc t
               in
                   unify ctx loc "proj" tt ttt;

                   case ttt of
                       TRec ltl =>
                           (case ListUtil.Alist.find op= ltl s of
                               NONE => error loc 
                                         ("label " ^ s ^ 
                                          " not in projection object type!")
                             | SOME tres => (Proj(s, ttt, ee), tres))
                     | _ => error loc "projection must be of record type"

               end

        (* FIXME if ff is a constructor, then expand in place and
           return the value. *)
        | E.App(ef, ea, _) =>
               let 
                 val (ff, ft) = elab ctx ef
                 val (aa, at) = elab ctx ea
                 val dom = new_evar ()
                 val cod = new_evar ()
               in
                 unify ctx loc "app:function" ft (Arrow (false, [dom], cod));
                 unify ctx loc "app:arg" at dom;
                 (App (ff, [aa]), cod)
               end

        | E.Constrain(e, t) =>
               let 
                   val (ee, tt) = elab ctx e
                   val tc = elabt ctx loc t

               in
                   unify ctx loc "constraint" tt tc;
                   (ee, tc)
               end

        | E.Andalso (a,b) =>
               elab ctx (E.If (a, b, Initial.falseexp loc), loc)

        | E.Orelse (a,b) =>
               elab ctx (E.If (a, Initial.trueexp loc, b), loc)

        | E.Andthen (a, b) => 
               elab ctx (E.If (a, (E.Seq (b, (E.Record nil, loc)), loc),
                                    (E.Record nil, loc)), loc)

        | E.Otherwise (a, b) => 
               elab ctx (E.If (a, 
                                    (E.Record nil, loc),
                                    (E.Seq (b, (E.Record nil, loc)), loc)), loc)

        | E.If (cond, tt, ff) =>
               elab ctx
               (E.Case ([cond],
                        [([Initial.truepat], tt),
                         ([Initial.falsepat], ff)], NONE), loc)

        | E.Case (es, m, default) =>
               let 
                 val def = case default of
                   SOME f => f
                 | NONE => 
                     fn () =>
                     let 
                       val warnstring = 
                         ("maybe inexhaustive match(case) at " ^ ltos loc)

                       val rexp = (EL.Raise (Initial.matchexp loc), loc)
                     in
                       if !warnmatch
                       then (EL.Seq((EL.CompileWarn warnstring, loc),
                                    rexp), loc)
                       else rexp
                     end

                   (* force case args to be variables, if they aren't. *)
                   fun force nil nc acc =
                            Pattern.elaborate true elab elabt nc loc
                                 (rev acc, m, def)
                     | force ((E.Var (E.Id v), _)::rest) nc acc = 
                            force rest nc (v::acc)
                     | force (e::rest) nc acc =
                            let
                              val (ee, tt) = elab ctx e
                              val s = newstr "case"
                              val sv = V.namedvar s
                              val nctx = C.bindv ctx s (mono tt) sv
                              val (ein, tin) = force rest nctx (s::acc)
                            in
                              (Let(Val (mono(sv, tt, ee)),
                                   ein), tin)
                            end
               in
                   force es ctx nil
               end

(*
        | E.Sham (wv, e) => 
            let
                val wvv = V.namedvar (case wv of
                                          NONE => "sham_unused"
                                        | SOME s => s)
                val nctx = (case wv of
                                NONE => ctx
                              | SOME wv => C.bindw ctx wv wvv)

                val (ee, tt) = elab nctx here e
            in
                case ee of
                    Value va => (Value ` Sham(wvv, va), Shamrock (wvv, tt))
                  | _ => error loc "sham expects a value, got expression"
            end

        (* could be "hold" or "held" depending on whether 
           the body is a value. *)
        | E.Hold e =>
            let
                val there = new_wevar ()
                val (ee, tt) = elab ctx there e
            in
                case ee of
                    Value va => (Value ` Hold(there, va), At (tt, there))
                  | _ => 
                    let
                        val nv = V.namedvar "h"
                    in
                        unifyw ctx loc "non-value hold" here there;
                        (Let(Bind(Val, mono(nv, tt, ee)),
                             Value ` Hold(here, Var nv)),
                         At(tt, here))
                    end
            end
*)

        | E.Raise e =>
            (case C.con ctx Initial.exnname of
                 (0, Typ exnt, Extensible) =>
                     let 
                         val (ee, tt) = elab ctx e
                         val ret = new_evar ()
                     in
                         unify ctx loc "raise" tt exnt;
                         (Raise (ret, ee), ret)
                     end
               | _ => error loc "exn type not declared???")

        | E.Handle (e1, pel) =>
            (case C.con ctx Initial.exnname of
              (0, Typ exnt, Extensible) =>
                let
                    val es = newstr "exn"
                    val ev = V.namedvar es
                        
                    val (ee, tt) = elab ctx e1

                    val mctx = C.bindv ctx es (mono exnt) ev

                    (* re-raise exception if nothing matches *)
                    fun def () =
                        (EL.Raise (EL.Var (E.Id es), loc), loc)
                        
                    (* XXX5 and world.. 
                       (this DOES include the world, right? -  6 Sep 2007) *)
                    val (match, mt) = 
                        Pattern.elaborate true elab elabt mctx loc
                           ([es], ListUtil.mapfirst ListUtil.list pel, def)
                in
                    unify ctx loc "handle" tt mt;
                    (Handle(ee, tt, ev, match), tt)
                end
            | _ => error loc "exn type not declared???")

        | E.CompileWarn s =>
               (Primapp(Primop.PCompileWarn s, [], []), TRec nil)

        (* makes slightly nicer code
           (nb, means that sequence-unit applies to do as well) *)
        | E.Let ((E.Do e, loc), e2) => elab ctx (E.Seq(e, e2), loc)

        | E.Let (d, e) =>
               let
                   val (dd, nctx) = elabd ctx d
                   val (ee, t) = elab nctx e
               in
                   (foldr Let ee dd, t)
               end

        | E.ECmd (p, c) =>
          let 
              val pp =
                  (case p of
                        SOME p => PSSet (PrioSet.singleton (elabpr ctx loc p))
                      | NONE => new_psevar ())
              val (ec, t, (pr1, pr2, pr3)) = elabcmd ctx pp (c, loc)
          in
              print "cmd (";
              printc ec;
              print "): ";
              printps pp;
              print "=";
              printps pr1;
              print " ";
              printps pr2;
              print " ";
              printps pr3;
              print "\n";
              unifyps loc "priority set command expression" pr1 pp;
              (Cmd (pp, ec), TCmd (t, (pr1, pr2, pr3)))
          end

        | E.PFn (pps, ps, e) => raise (Elaborate "Pfn unimplemented")
  (* XXX4 TODO come back to this later
          let val cpps = List.map (fn PPVar s => (s, [])
                                  | PPConstrain spcs => spcs
                                  )
                                  pps
              val (pvs, pcs) = ListPair.unzip cpps
              val pvars = List.map V.named_var pvs
              val pcons = List.concat pcs
              val var = V.named_var "anonpfn"
                                    
          List.foldl (fn (pp,  =>
                         case pp of
                             PPVar s => 
   *)
        | E.PApply (e, p) =>
          let (* val _ = print "elaborating e\n" *)
              val (ee, t) = elab ctx e
              (* val _ = print "elaborating p\n" *)
              val pp = elabpr ctx loc p
              (* val _ = print "done\n" *)
              val priov = new_pevar ()
          in
              (* XXX4 is this casing thing OK? *)
              case t of
                  TForall ([pv], cons, tt) =>
                  let val cons' = List.map (* (fn PCons (p1, p2) =>
                                               let val _ = print "before : "
                                                   val _ = printp p1
                                                   val _ = print " <= "
                                                   val _ = printp p2
                                                   val _ = print "\n"
                                                   val PCons (p1', p2') =
                                                       psubsc1 pp pv
                                                               (PCons (p1, p2))
                                                   val _ = print "after : "
                                                   val _ = printp p1'
                                                   val _ = print " <= "
                                                   val _ = printp p2'
                                                   val _ = print "\n"
                                               in
                                                   PCons (p1', p2')
                                               end) *)
                                      (psubsc1 pp pv)
                                      cons
                  in
                      List.app (fn PCons (p1, p2) =>
                                   check_constraint ctx loc p1 p2)
                               cons';
                      (PFApp (ee, pp), psubst1 pp pv tt)
                  end
                | TForall _ => error loc "only one priority argument supported"
                | _ => error loc "not a forall"
          end

  and elabcmd ctx (pr: IL.prioset) ((i, loc): E.cmd) =
      case i of
          E.Spawn (p', c) =>
          let val p' = elabpr ctx loc p'
              val pp' = PSSet (PrioSet.singleton p')
              val (ec, t, (pr', pr1, pr2)) = elabcmd ctx pp' c
          in
              unifyps loc "priority set spawn" pr' pp';
              (Spawn (p', t, ec), TThread (t, pr1), (pr, pr, pr))
          end
        | E.Sync e =>
          let val (ee, t) = elab ctx e
              val tint = new_evar ()
              val psint = new_psevar ()
          in
              print "sync: ";
              printps psint;
              print "\n";
              unify ctx loc "sync argument" t (TThread (tint, psint));
              pscstr_cons pr psint;
              (Sync ee, tint, (pr, pr, pr))
          end
        | E.Poll e =>
          let val (ee, t) = elab ctx e
              val tint = new_evar ()
              val psint = new_psevar ()
              val _ = unify ctx loc "poll argument" t (TThread (tint, psint))
              val t = ((case C.con ctx "option" of
                            (kind, Lambda f, _) =>
                            if kind = 1
                            then f [tint]
                            else error loc "Should not happen"
                          | _ => error loc "Should not happen")
                       handle Context.Absent _ =>
                              error loc "Should not happen")
          in
              print "poll: ";
              printps psint;
              print "\n";
              (Poll ee, t, (pr, pr, pr))
          end
        | E.Cancel e =>
          let val (ee, t) = elab ctx e
              val tint = new_evar ()
              val psint = new_psevar ()
          in
              print "cancel: ";
              printps psint;
              print "\n";
              unify ctx loc "cancel argument" t (TThread (tint, psint));
              (Cancel ee, TRec [], (pr, pr, pr))
          end
        | E.IRet e =>
          let val (ee, t) = elab ctx e
          in
              print "ret: ";
              printps pr;
              print "\n";
              (Ret ee, t, (pr, pr, pr))
          end
        | E.Change p' => 
          let val p' = elabpr ctx loc p'
              val pp' = PSSet (PrioSet.singleton p')
              val pr' = new_psevar ()
          in
            print "change: ";
            printps pr;
            print " ";
            printps pr';
            print " ";
            printps pp';
            print "\n";
            pscstr_gen pr pr' pp';
            (Change p', TRec [], (pr, pr', pp'))
          end
        | E.IBind is => elabbind ctx pr is 

  and elabbind ctx (pr: IL.prioset) (is, li) =
      case is of
          [] =>
          (* Treat the last instruction as just another binding and return its
             value. May introduce an unnecessary binding, but oh well. *)
          (let val (_, loc) = li
               val dvar = "retval__"
               val v = V.namedvar dvar
               val (ii, t) = elab ctx li
               val tint = new_evar ()
               val pr1 = new_psevar ()
               val pr2 = new_psevar ()
               val pr3 = new_psevar ()
           in
               print "bind last (";
               printe ii;
               print "): ";
               printps pr1;
               print " ";
               printps pr2;
               print " ";
               printps pr3;
               print " ";
               print "\n";
               unify ctx loc "bind argument" t (TCmd (tint, (pr1, pr2, pr3)));
               pscstr_gen pr1 pr2 pr3;
               (Bind (v, ii, Ret (Value (Var v))), tint, (pr1, pr2, pr3))
           end)
        | (s, i as (_, loc))::rest =>
          (* Bind the elaborated instruction in the elaborated remainder *)
          (let val v = V.namedvar s
               val (ii, t) = elab ctx i
               val tint = new_evar ()
               val pr1 = new_psevar ()
               val pr2 = new_psevar ()
               val pr3 = new_psevar ()
               val pr4 = new_psevar ()
               val pr7 = new_psevar ()
               val ctx' = C.bindv ctx s (mono tint) v
               val (cmd, t', (pr4', pr5, pr6)) = elabbind ctx' pr4 (rest, li)
           in
               print "bind (";
               printe ii;
               print "): ";
               printps pr1;
               print " ";
               printps pr2;
               print " ";
               printps pr3;
               print " ";
               printps pr7;
               print " ";
               print "\n";
               unify ctx loc "bind argument" t (TCmd (tint, (pr1, pr2, pr3)));
               unifyps loc "priority set binding" pr pr1;
               unifyps loc "priority set binding" pr4 pr4';
               pscstr_gen pr1 pr7 pr6;
               pscstr_sup pr4 pr3;
               pscstr_sup pr7 pr2;
               pscstr_sup pr7 pr5;
               (Bind (v, ii, cmd), t', (pr1, pr7, pr6))
           end)

  and mktyvars ctx tyvars =
      foldl (fn (tv, ctx) => C.bindc ctx tv (Typ ` new_evar ()) 0 Regular)
            ctx tyvars

  and elabf ctx 
            (arg : string)
            (clauses : (EL.pat list * EL.typ option * EL.exp) list) 
            loc =
      let in
          (* ensure clauses all have the same length *)
          ListUtil.allpairssym (fn ((a, _, _), (b, _, _)) =>
                                length a = length b) clauses
               orelse error loc 
                  "clauses don't all have the same number of curried args";

          (* now we make big nested function *)

          (* p11 p12 p13 ... : t1 = e1 
             p21 p22 p23 ... : t2 = e2
              ...

             becomes:

             let fun f2 (x2) =
                 let fun f3 (x3) = ...

                     (case x , x2 , x3 of
                        p11 p12 p13 => e1
                        p21 p22 p23 => e2
                          ...
                        _ _ _ => raise Match)
                     : t1 : t2 : ... : tn 


                 in f3
                 end
             in f2 
             end

             *)
          (case clauses of
            [([pat], to, e)] =>
              let
                  (* base case *)
                  val (exp, tt) = 
                      Pattern.elaborate true elab elabt ctx loc
                         ([arg],
                          [([pat], e)],
                          (fn () =>
                           let 
                             val warnstring = 
                               ("maybe inexhaustive match(fun) at " ^ ltos loc)
                             val rexp = (EL.Raise (Initial.matchexp loc), loc)
                           in
                             if !warnmatch
                             then (EL.Seq((EL.CompileWarn warnstring, loc),
                                          rexp), loc)
                             else rexp
                           end))
              in
                  (case to of
                       SOME t => unify ctx loc 
                                   "codomain type constraint on fun" tt
                                   (elabt ctx loc t)
                     | _ => ());
                  (exp, tt)
              end
          | nil => (* raise Elaborate "impossible: *no* clauses in fn" *)
                   elab ctx (EL.Raise (Initial.matchexp loc), loc)
          | _ =>
               let
                   (* we already have an arg since we're inside the
                      function body, so that's where all this 'tl'
                      stuff comes from *)
                   val args = arg :: 
                       map (fn p =>
                            (case p of
                                 E.PVar s => newstr s
                               | E.PAs (s,_) => newstr s
                               | _ => newstr "cur")) ` tl ` #1 ` hd clauses

                   (* all constraints on fun body *)
                   val constraints =
                       List.mapPartial #2 clauses

                   val columns = map (fn (pl, _, e) => (pl, e)) clauses

                   fun buildf nil =
                       (* build the case, slapping all of the
                          body constraints on its outside *)
                       (* XXX5 
                          allow world constraints *)
                       foldr (fn (t, e) => (E.Constrain(e, t), loc)) 
                             (E.Case (map (fn a => (E.Var (E.Id a), loc)) args, 
                                      columns, NONE), loc)
                             constraints
                     | buildf (x::rest) =
                       let
                           val fc = newstr "fc"
                       in
                         (* XXX inline? *)
                           (E.Let((E.Fun { inline = false, 
                                           funs = [(nil, fc, [([E.PVar x], NONE,
                                                               buildf rest)])] }, loc),
                                  (E.Var (E.Id fc), loc)),
                            loc)
                       end
               in
                   elab ctx ` buildf ` tl args
               end)

      end handle Pattern.Pattern s => 
            error loc ("Pattern compilation failed: " ^ s)

  and elabds ctx nil = (nil, ctx)
    | elabds ctx ((d : EL.dec) :: rest) =
    let 
      val (ds, ctx) = elabd ctx d
      val (rs, ctx) = elabds ctx rest
    in
      (ds @ rs, ctx)
    end
(*
  (* trivial *)
  and elabk EL.KJavascript = IL.KJavascript
    | elabk EL.KBytecode = IL.KBytecode
*)

  (* return a new context, and an il.dec list *)
  and elabd ctx ((d, loc) : EL.dec) 
    : IL.dec list * C.context =  
    case d of
      E.Do e => 
        let val (ee, tt) = elab ctx e
        in
          (if !sequenceunit
           then unify ctx loc "sequence unit" tt (IL.TRec nil)
           else ());
          ([Do ee], ctx)
        end

    | E.Type (nil, tv, typ) =>
          let val t = elabt ctx loc typ
          in ([], C.bindc ctx tv (Typ t) 0 Regular)
          end

    | E.Tagtype t =>
          let
              val tv = V.namedvar t

              (* bind type, note that it is mobile *)
              val ctx = C.bindc ctx t (Typ (TVar tv)) 0 Extensible
              (* val ctx = C.bindmobile ctx tv *)
          in
              ([Tagtype tv], ctx)
          end

(*
    | E.ExternWorld (k, l) => ([ExternWorld (l, elabk k)], C.bindwlab ctx l ` elabk k)

    | E.ExternVal (atvs, id, ty, wo, lo) =>
          let
            
            (* use imported label if given, otherwise it's the same as the id *)
            val implab = case lo of NONE => id | SOME l => l

            (* might be modal or valid. *)
            val (varsort, actx) =
              case wo of
                EL.Modal w => (Modal ` elabw ctx loc w, ctx)
              | EL.Valid wid =>
                  let val wv = V.namedvar wid
                  in (Valid ` wv, C.bindw ctx wid wv)
                  end

            fun checkdups atvs =
              ListUtil.alladjacent op <> `
              ListUtil.sort String.compare atvs
              orelse 
              error loc ("duplicate type vars in extern val declaration (" ^ id ^ ")")

            (* no dup tyvars *)
            val _ = checkdups atvs
              
            (* augment atvs with real variables too *)
            val atvs = map (fn x => (x, V.namedvar x)) atvs
             
            (* put tyvars in context for elaboration of type *)
            val actx =
              foldl (fn ((s, x),c) =>
                     C.bindc c s (Typ (TVar x)) 0 
                     Regular) actx atvs

            (* now elaborate the type. *)
            val tt = elabtex actx NONE loc ty
            val ptt =
              Poly ({ worlds = nil (* XXX5 *),
                      tys = map #2 atvs }, tt)

            val v = V.namedvar id

          in
            (* XXX5 allow worlds *)
            ( [ExternVal(Poly({worlds=nil, tys=map #2 atvs}, 
                              (implab, v, tt, varsort)))],
             C.bindex ctx (SOME id) ptt v Normal varsort)
          end

    | E.ExternType (nil, s, so) =>
          let
            val v = V.namedvar s
            val lab = case so of NONE => s | SOME s' => s'
          in
            ([ExternType (0, lab, v)],
             C.bindc ctx s (Typ ` TVar v) 0 Regular)
          end

    (* To support extern types of higher kind, we need to support
       TPolyVar... save it for later if desired. *)
    | E.ExternType _ => error loc "extern types must have kind 0"
*)

    (* some day we might add something to 'ty,' like a string list
       ref so that we can track the exception's history, or at least
       a string with its name and raise point. *)
    | E.Exception (e, ty) => elabd ctx (E.Newtag(e, ty, Initial.exnname), loc)

    (* A tag can be declared to be modal or valid. If it's valid, it must have
       a mobile body. *)
    | E.Newtag (tag, dom, ext) =>
       (case C.con ctx ext of
          (0, Typ (cod as TVar ev), Extensible) =>
            let
                (* need to generate the tag as well as
                   a constructor function *)
                val tagv = V.namedvar (tag ^ "_tag")
                val d = elabt ctx loc 
                     (case dom of
                          NONE => 
                              error loc 
                              "bug: nullary phase did not write newtag decl"
                        | SOME x => x)

                val ctor = V.namedvar tag
                val carg = V.namedvar "tagarg"

                val fntype = Arrow(true, [d], cod)
                (* the constructor function *)
                fun fnvalue tag =
                   FSel (0,
                         Fns
                         [{ name = ctor, arg = [carg],
                            dom = [d], cod = cod, 
                            inline = true,
                            recu = false, total = true,
                            body = Tag(Value ` Var carg, Value tag) }])

            in(*
              if mkvalid
              then
                let 
                  (* Tag type must be mobile if this is a vtag *)
(*                  val () = require_mobile ctx loc "newvtag" d *)
                  val mtagv = V.namedvar (tag ^ "_here")

                  val wv = V.namedvar "newtag0"
                in
                  ([Newtag (mtagv, d, ev),
                    (* make tag valid, because it is mobile *)
                    Val (mono ` (tagv, TTag (d, ev), Value ` Var mtagv)),
                    (* then declare the constructor valid *)
                    Letsham(Poly ({worlds = nil, tys = nil},
                                  (ctor, (wv, fntype), 
                                   Sham (wv, fnvalue (Polyuvar { worlds = nil,
                                                                 tys = nil,
                                                                 var = tagv })))))
                    ],
                    (* now bind constructor validly *)
                    C.bindex ctx (SOME tag)
                          (mono ` Arrow(true, [d], cod))
                          ctor
                          (* use the valid tag to destruct *)
                          (Tagger (Polyuvar { worlds = nil, tys = nil, var = tagv }))
                          (C.Valid wv)
                   )
                end
              else *)
                ([Newtag (tagv, d, ev),
                  bindval ` mono ` (ctor, fntype, Value ` fnvalue ` Var tagv)],
                 (* bind tag locally (in IL only) *)
                 C.bindex ctx (SOME tag)
                            (mono ` Arrow(true, [d], cod))
                            ctor
                            (* use the modal var to destruct *)
                            (Tagger ` Var tagv)
                            (* (C.Modal here) *))
            end
        | _ => error loc (ext ^ " is not an extensible type"))

    | E.Datatype (atvs, unsorted) =>
          let
            (* datatype (a, b, c) t = A of t | B of a | C of t1
               and                u = D of u | E of b | F

               syntax enforces uniformity restriction.
               prepass ensures every arm is 'of' some type.

                              tyvars       type
               Datatype of  string list * (string * 
                              ctor      members
                            (string * typ option) list) list
               *)

              (* put in sorted order. *)
              val dl =
                  ListUtil.sort (ListUtil.byfirst String.compare) unsorted

              (* check: no duplicate datatype names *)
              val _ =
                  ListUtil.alladjacent
                     (fn ((a, _), (b, _)) => a <> b) dl
                  orelse error loc "duplicate type names in datatype decl"

              (* check: no duplicate tyvars *)
              val _ =
                  ListUtil.alladjacent op <> `
                    ListUtil.sort String.compare atvs
                  orelse error loc "duplicate type vars in datatype decl"

              (* check: no overlap between tyvars and datatypes *)
              val _ =
                  ListUtil.alladjacent op <> `
                    ListUtil.sort String.compare (atvs @ map #1 dl)
                  orelse error loc 
                    "tyvar and datatype share same name in datatype decl"

              (* check: no duplicated constructors *)
              val _ =
                  app (fn (dt, arms) =>
                       let
                           val sorted =
                               ListUtil.sort (ListUtil.byfirst 
                                              String.compare) arms
                       in
                           ListUtil.alladjacent
                             (fn ((a,_),(b,_)) => a <> b) sorted
                           orelse error loc
                                  ("duplicated constructor in datatype " ^
                                   dt); ()
                       end) dl

              (* augment with index and recursive var *)
              (* XXX note that we use the basename of the variable
                 created in order to determine the external name for
                 this type during pretty printing. This is nasty, but
                 to get the best results, use 'dt' as the basename
                 for the bound var. *)
              val dl =
                  ListUtil.mapi (fn ((dt, arms), n) =>
                                 (dt, arms, n,
                                  V.namedvar (dt 
                                              (* ^ "_" ^ itos n ^ "_" *)))) dl

              (* augment atvs with real variables too *)
              val atvs = map (fn x => (x, V.namedvar x)) atvs

                  
              (* put tyvars in context for arms *)
                  
              val actx = 
                  foldl (fn ((s, x),c) =>
                         C.bindc c s (Typ (TVar x)) 0 Regular) ctx atvs

              (* bind each datatype name to the corresponding
                 recursive variable for the purpose of elaborating
                 the arms. *)

              val actx = 
                  foldl (fn ((dt, _, _, v), c) =>
                         C.bindc c dt (Typ (TVar v)) 0 Regular) actx dl

              fun gen_arminfo NONE = NonCarrier
                | gen_arminfo (SOME t) = 
                let
                  val tt = elabt actx loc t
                in
                  (* PERF this is very conservative now
                     (got the post-bug jitters), mainly
                     designed to catch the list datatype.
                     With the current backend it could be
                     extended to all sorts of stuff, like
                     ints, other definitely allocated
                     datatypes, etc...
                     *)
                  Carrier { carried = tt,
                            definitely_allocated = 
                            (case tt of
                               TRec (_ :: _ :: _) => true
                             | TVec _ => true
                             | TRef _ => true
                             | Arrow _ => true
                             | _ => false) }
                end

              (* elaborate each arm *)
              val dl =
                  map (fn (dt, arms, n, v) =>
                       (dt, 
                        ListUtil.mapsecond gen_arminfo arms,
                        n, v)) dl

              (* make body of mu *)
              val mubod =
                  map (fn (_, arms, _, v) => (v, Sum arms)) dl
                  
              (* make il con for each, consuming n *)
              val dl = 
                  map (fn (dt, arms, n, v) =>
                       (dt, arms, Mu(n, mubod), v)) dl
                       

              (* outside the mu, we need to substitute the mu
                 itself for the datatype type variable. *)
              val musubst =
                  Subst.tsubst `
                  Subst.fromlist
                  (map (fn (_, _, mu, v) =>
                        (v, mu)) dl)

              (* don't need v any more *)
              val dl = map (fn (dt, arms, mu, _) => (dt, arms, mu)) dl

              (* generate the wrapper Lambda that binds the
                 tyvars *)

              val kind = length atvs

              (* XXX from here on I only use #2 of atvs... *)

              fun wrapper body =
                  let
                      fun bs nil nil s = s
                        | bs ((_,v)::vrest) (tt::trest) s =
                          bs vrest trest ` V.Map.insert (s, v, tt)
                        | bs _ _ _ =
                          error loc 
                            "wrong number of type arguments to datatype"
                  in
                      Lambda (fn tl => 
                              Subst.tsubst (bs atvs tl V.Map.empty) body)
                  end

              (* setup done. now generate the new context and decls. *)

              (* first add the datatypes *)
              val nctx = 
                  foldl
                   (fn ((dt, _, mu), c) =>
                    C.bindc c dt (wrapper mu) kind Regular) ctx dl

              (* now bind all the constructors *)

              val atvs = map #2 atvs
                  

              (* generate a list:
                 (ctor string, ctor var, ctor type, ctor decl) *)
              val ctors = 
                  List.concat `
                  map (fn (dt, arms, mu) =>
                       map (fn (ctor, NonCarrier) => 
                            let
                              val cty = Poly({prios=nil, tys=atvs}, mu)

                              val v = V.namedvar ("ctor_null_" ^ ctor)

                              val arms = ListUtil.mapsecond (arminfo_map musubst) arms
                            in
                                (ctor, v, cty,
                                 Val (Poly({prios = nil, 
                                     tys = atvs},
                                    (v, mu, Roll(mu,
                                                 Inject(Sum arms, ctor, NONE))))))
                            end
 
                           | (ctor, Carrier { carried = ty, ... }) =>
                            let 
                                val arms = ListUtil.mapsecond (arminfo_map musubst) arms
                                val dom = musubst ty

                                val cty = 
                                  Poly({prios=nil,
                                        tys=atvs},
                                       (Arrow 
                                        (true (* yes total! *), 
                                         [dom], mu)))

                                val ctorf = V.namedvar ("ctor_" ^ ctor)
                                val x = V.namedvar "xdt"
                            in
                                (ctor, ctorf,
                                 (* type of constructor *)
                                 cty,
                                 (* injection value *)
                                 Val (Poly({prios = nil, tys = atvs},
                                            (ctorf,
                                             Arrow(true, [dom], mu),
                                             Value ` FSel (0,
                                                    Fns
                                                    [{ name = V.namedvar "notrec",
                                                       dom = [dom],
                                                       cod = mu,
                                                       arg = [x],
                                                       (* inline it! *)
                                                       inline = true,
                                                       recu = false,
                                                       total = true,
                                                       body =
                                                       Roll(mu,
                                                            Inject
                                                            (Sum arms, ctor, 
                                                             SOME ` Value ` Var x))}])))))
                            end) arms) dl

              (* bind the constructors. Constructors should be valid. *)
              val nctx =
                  foldl
                  (fn ((ctor, v, at, _),c) =>
                   C.bindex c (SOME ctor) at v Constructor) nctx ctors

          in
              (map #4 ctors, nctx)
          end

    | E.Type (tyvars, tv, typ) =>
          let
              val kind = length tyvars

              fun conf l =
                   if length l <> kind
                   then error loc "(bug) wrong number of args to Lambda"
                   else 
                       let val nc = 
                           ListPair.foldl 
                              (fn (tv, t, ctx) =>
                               C.bindc ctx tv (Typ t) 0 Regular) 
                              ctx (tyvars, l)
                       in
                           elabt nc loc typ
                       end
          in
              (* provisional instantiation of type, to make sure its
                 body is not bogus (unelaboratable) prima facie *)
              ignore ` conf (List.tabulate (kind, fn _ => new_evar ()));

              ListUtil.allpairssym op<> tyvars 
                 orelse error loc "duplicate tyvars in type dec";
              ([], C.bindc ctx tv (Lambda conf) kind Regular)
          end

    (* For functions, we also do automatic validity inference.
       
       Basically, since this is a value, we don't restrict the
       declaration to 'here'. Instead we elaborate it at an
       existential world, and then if that world is unrestricted at
       the end, we make the binding valid by introducing a shamrock
       and immediatley eliminating it.

       To explicitly declare a function at another world, then we just
       use type (judgment) annotation

       XXX The same should be true of val decls that are generalizable. *)
    | E.Fun { inline, funs = bundle } =>
          let

              val outer_context = ctx

              (* okay to have no clauses in a function, but there
                 should be at least one function in any mutually-recursive
                 bundle *)
              val  _ = List.null bundle 
                         andalso error loc "BUG: *no* fns in bundle?"

              val _ = ListUtil.allpairssym (fn ((_, f, _), (_, g, _)) =>
                                            f <> g) bundle
                         orelse error loc 
                             "duplicate functions in fun..and"
(*
              (* functions are values, so we elaborate at an existential
                 world to see if we can generalize (make the function valid) *)
              val atworld = new_wevar ()
*)

              (* make var for each fn *)
              val binds =
                  map (fn (tv, f, b) => 
                       let val vv = V.namedvar f
                           val dom = new_evar ()
                           val cod = new_evar ()
                       in
                           (tv, f, b, vv, dom, cod)
                       end) bundle

              (* to process the body of one function, we
                 bind the existential variables that appeared
                 before the function name, and bind all functions
                 at (mono) existential arrow type. *)
              fun onectx c tv =
                  let
                      val nc = 
                          foldl (fn ((_, f, _, vv, dom, cod), ct) =>
                                 C.bindv ct f (mono (Arrow(false, 
                                                            [dom],
                                                            cod))) vv)
                                c binds
                  in
                      mktyvars nc tv
                  end

              (* for each function, elaborate and return:
                 name, var,
                 arg variable,
                 domain type
                 codomain type
                 il expression body *)
              fun onef (tv, f, clauses, vv, dom, cod) =
                  let
                      val c = onectx ctx tv
                      val x = newstr "x"
                      val xv = V.namedvar x
                      val nc = C.bindv c x (mono dom) xv

                      val (exp, tt) = elabf nc x clauses loc
                  in
                      unify c loc "fun body/codomain" tt cod;
                      (f, vv, xv, dom, cod, exp)
                  end

              (* collect up elaborated functions and
                 forall-quantified vars *)
              fun folder ((f, vv, x, dom, cod, exp),
                          (fs, efs, tpolys, wpolys)) =
                  let
                    (* it's okay to make these two calls to polygen,
                       since if we generalize something in dom it
                       will be set Bound to that tyvar in cod. But
                       perhaps polygen should take a list of types. *)
                      val { t = dom, tl = dpt, wl = dpw } = polygen outer_context dom
                      val { t = cod, tl = cpt, wl = cpw } = polygen outer_context cod
                  in
                      ({ name = vv,
                         arg = [x],
                         dom = [dom],
                         (* PERF only if requested by code (which generally should 
                            only be done in compiler support code, like the
                            implementation of plus). We should detect here some
                            other functions that would benefit from inlining *)
                         inline = inline,
                         (* PERF detect actual recursiveness, totality *)
                         recu = true,
                         total = false,
                         cod = cod,
                         body = exp } :: fs, 
                       (f, vv, Arrow(false, [dom], cod)) :: efs,
                       dpt @ cpt @ tpolys,
                       dpw @ cpw @ wpolys)
                  end

              val (fs, efs, tps, wps) = 
                  foldl folder (nil, nil, nil, nil) ` map onef binds

              (* check if atworld can be generalized. if so,
                 then the declaration will be valid. We already
                 made sure this type didn't get generalized above. *)
(*               val maybevalid = polywgen outer_context *)

              (* we'll generalize both the binding of the bundle
                 and the binding of each of the projections in the same way (this way). 
                 
                 We generalize both type variables and world variables.
                 *)
              fun mkpoly tps wps at = Poly({prios = wps, tys = tps}, at)

              (* rebuild the context with these functions
                 bound polymorphically *)
              fun mkcontext ((f, vv, at), cc) =
                  (* (case maybevalid of
                       (* not valid. *)
                       NONE => C.bindv cc f (mkpoly tps wps at) vv atworld
                       (* valid. wv might appear within at. *)
                     | SOME wv => *)
                  C.bindex cc (SOME f) (mkpoly tps wps at) vv IL.Normal (*(C.Valid wv)) *)

              val fctx = foldl mkcontext outer_context efs
(*
              val () =
                let val n = StringUtil.delimit "_" (map (V.basename o #name) fs)
                in
                  case maybevalid of
                    NONE => () (* print (n ^ " is not valid\n") *)
                  | SOME _ => print (n ^ " is valid\n")
                end
*)
              (* bind as regular value or as a valid value *)
              val bind = 
                  (*case maybevalid of
                      NONE => (fn Poly ({ worlds, tys }, (v, t, e)) =>
                               Leta(Poly ({worlds = worlds, tys = tys},
                                          (v, t, Hold (atworld, e)))))
                    | SOME wv => (fn Poly ({ worlds, tys }, (v, t, e)) =>
                                  Letsham(Poly ({worlds = worlds, tys = tys},
                                                (v, (wv, t), Sham (wv, e))))
                                  ) *)
                  (fn Poly ({prios, tys}, (v, t, e)) =>
                      Val (Poly ({prios = prios, tys = tys}, (v, t, e))))
              
              (* we bind the bundle as a var or uvar.. *)
              val PolyOccur = Polyvar
(*
                  case maybevalid of
                    NONE => Polyvar
                  | SOME _ => Polyuvar
*)
          in
            (*
            print "binding fun:\n";
            Layout.print(Context.ctol fctx, print);
            print "\n";
            *)
              (* if just one, then we want to produce better code: *)
              case fs of
                 [ f as { name, arg, dom, inline, recu, total, cod, body } ] =>
                   ([bind ` mkpoly tps wps ` (name, Arrow (false, dom, cod), 
                                              Value (FSel(0, Fns [f])))], fctx)
                | _ => 
                   let val bundv = V.namedvar ` StringUtil.delimit "_" (map (V.basename o #name) fs)
                   in
                     ( 
                      (* the bundle... *)
                      (bind ` mkpoly tps wps ` (bundv, Arrows ` map (fn { dom, cod, ... } => 
                                                                     (false, dom, cod)) fs,
                                                Value (Fns fs))) ::
                      (* then bind the projections... *)
                      ListUtil.mapi (fn ({ name, dom, cod, ... }, i) =>
                                     let val tps = tps (* map V.alphavary ps *)
                                          (* (would also need to rename through dom/cod) *)
                                     in
                                       bind ` mkpoly tps wps ` (name, 
                                                                Arrow (false, dom, cod), 
                                                                Value (FSel(i, 
                                                                     PolyOccur { tys = map TVar tps,
                                                                                 prios = map PVar wps,
                                                                                 var = bundv })))
                                     end) fs,
                      fctx)
                   end
          end

(*    | E.Letsham (tyvars, v, exp) => error loc "letsham unimplemented" *)
(*
    | E.Letsham (tyvars, v, exp) =>
         let
             val nctx = mktyvars ctx tyvars

             val (ee, tt) = elab nctx exp

             val wv = V.namedvar "ls_wv"
             val t = new_evar ()
             val () = unify ctx loc "letsham" tt (Shamrock(wv, t))

             val polydec = (case ee of
                                Value v => SOME v
                              | _ => NONE)

             val { t = tt, tl = tps, wl = wps } = 
                 if isSome polydec
                 then polygen ctx tt here
                 else { t = tt, tl = nil, wl = nil }

             val vv = Variable.namedvar v

             val ctx = C.bindex ctx (SOME v) (Poly ({worlds = wps,
                                                     tys = tps}, t)) vv Normal 
                                             (C.Valid wv)

             val va = Variable.namedvar "letsham_serialize"
         in
             (* and it requires a value; serialize if it's not one *)
             case polydec of
                 NONE =>
                     ([Bind(Val, mono(va, tt, ee)),
                       Letsham ` mono (vv, (wv, t), Var va)], ctx)
               | SOME valu => 
                     ([Letsham ` Poly({ worlds = wps, tys = tps },
                                      (vv, (wv, t), valu))], ctx)
         end

    | E.Leta (tyvars, v, exp) =>
         let
             val nctx = mktyvars ctx tyvars

             val (ee, tt) = elab nctx exp
             val there = new_wevar ()
             val t = new_evar ()
                 
             val () = unify ctx loc "leta" tt (At(t, there))

             val polydec = (case ee of
                                Value v => SOME v
                              | _ => NONE)

             val { t = tt, tl = tps, wl = wps } = 
                 if isSome polydec
                 then polygen ctx tt there
                 else { t = tt, tl = nil, wl = nil }

             val vv = Variable.namedvar v

             val ctx = C.bindex ctx (SOME v) (Poly ({worlds = wps,
                                                     tys = tps}, t)) vv Normal 
                                             (C.Modal there)


             val va = Variable.namedvar "leta_serialize"
         in
             (* and it requires a value; serialize if it's not one *)
             case polydec of
                 NONE =>
                     ([Bind(Val, mono(va, tt, ee)),
                       Leta ` mono (vv, t, Var va)], ctx)
               | SOME valu => 
                     ([Leta ` Poly({ worlds = wps, tys = tps },
                                   (* XXX5 is this supposed to be "t" or "t at w" (= tt)? (also above) *)
                                   (vv, t, valu))], ctx)
         end
*)

    (* val and put bindings *)
    (* XXX5 validitization is not implemented for
       val bindings. this should work like the fun case.
       also: some things are not currently detected as values (constructor
       applications, for instance).
       *)
    | E.Val (tyvars, E.PVar v, exp) =>
          let
              (* simply bind tyvars;
                 let generalization actually determine the type. 
                 if we want to have these type vars act like SML,
                 we can check after the decls are over that each
                 one is still free and generalizable. 
                 XXX5 we let these sit in the exported context --
                      that's definitely wrong!
                      
                 how so? the identifiers are certainly gone because
                 we don't use nctx after elaborating the body.
                 *)
              val nctx = mktyvars ctx tyvars

              val (ee, tt) = elab nctx exp
              val polydec = (case ee of
                               Value _ => true
                             | _ => false)


              val { t = tt, tl = tps, wl = wps } = 
                if polydec
                then polygen ctx tt
                else { t = tt, tl = nil, wl = nil }

              val vv = Variable.namedvar v

              val ctx = C.bindex ctx (SOME v) (Poly ({prios = wps,
                                                      tys = tps}, tt)) vv Normal 

          in
              ([Val (Poly({ prios = wps, tys = tps }, (vv, tt, ee)))], ctx)
          end

    (* anything but a variable is syntactic sugar. *)
    | E.Val (tyvars, E.PWild, exp) => elabd ctx (E.Val (tyvars, E.PVar ` newstr "wild", exp), loc)

    | E.Val (tyvars, E.PAs (v, p), exp) =>
            let
              (* val (x as p) = e
                 
                 means
                 
                 val x = e
                 val p = x
                 *)

              val (decls, ctx) = elabd ctx (E.Val (tyvars, E.PVar v, exp), loc)
              val (decls2, ctx) = elabd ctx (E.Val (tyvars, p, (E.Var (E.Id v), loc)), loc)
            in
              (decls @ decls2, ctx)
            end
    | E.Val (tyvars, E.PConstrain (p, t), exp) =>
            elabd ctx (E.Val (tyvars, p, (E.Constrain(exp, t), loc)), loc)
    | E.Val (_, E.PApp _, _) => error loc "app patterns are refutable"
    | E.Val (_, E.PConstant _, _) => error loc "constant patterns are refutable"
    | E.Val (_, E.PWhen _, _) => error loc "when patterns are refutable"
    | E.Val (tyvars, E.PRecord spl, exp) =>
            let
              (* val (a, b, c) = e

                 means
                 
                 val x = e
                 val a = #a/3 e
                 val b = #b/3 e
                 val c = #c/3 e
                 
                 *)
              val t = E.TNum ` length spl
              val v = newstr "brec"
              val (decls, ctx) = elabd ctx (E.Val (tyvars, E.PVar v, exp), loc)

              fun projs ctx nil = (nil, ctx)
                | projs ctx ((l, p) :: rest) = 
                let
                    val (decls, ctx) = elabd ctx (E.Val (tyvars, p, (E.Proj(l, t, (E.Var (E.Id v), loc)), loc)), loc)
                  val (decls2, ctx) = projs ctx rest
                in
                  (decls @ decls2, ctx)
                end
              val (declsp, ctx) = projs ctx spl
            in
              (decls @ declsp, ctx)
            end
    | E.WFun (s, ppats, pats, tyo, body) =>
      let val cpps = List.map (fn E.PPVar s => (s, [])
                              | E.PPConstrain spcs => spcs
                              )
                              ppats
          val (pvs, pcs) = ListPair.unzip cpps
          val v = V.namedvar s
          val pvars = List.map V.namedvar pvs
          val ctx' = ListPair.foldl (fn (v, s, ctx) => C.bindp ctx s v)
                                    ctx (pvars, pvs)
          val pcons = List.map (fn (p1, p2) =>
                                   PCons (elabpr ctx' loc p1,
                                          elabpr ctx' loc p2))
                               (List.concat pcs)
          val ctx' = List.foldl (fn (PCons pc, ctx) =>
                                    C.bindpcons ctx pc)
                                ctx'
                                pcons

          (* Circuitous way to reuse the Fun elaboration code *)
          (* Generate a temporary evar for the type of the recursive call *)
          val temp_t = TForall (pvars, pcons, new_evar ())
          (* Bind the real name with the evar, elaborate the
             priority-monomorphic function with a new name, let elabd
             tell us the actual type *)
          val s' = "cgen_temp_fun__"
          val ctx' = C.bindv ctx' s (mono temp_t) v
          val funs = [([], s', [(pats, tyo, body)])]
          val (decls, ctx'') = elabd ctx' ((E.Fun {inline = false, funs = funs}),
                                           loc)

          (* Find out what the type of s' was. *)
          val (Poly ({prios, tys}, t), v, stat) = C.var ctx'' s'

          (* Now bind the real name with the real type and elaborate again. *)
          val t' = Poly ({prios = prios (* @ pvars *), tys = tys},
                         (TForall (pvars, pcons, t)))
          val ctx' = C.bindv ctx' s t' v
          val (decls, ctx'') = elabd ctx' ((E.Fun {inline = false, funs = funs}),
                                           loc)
          val ctx'' = C.bindex ctx (SOME s) t' v stat
      in
          case decls of
              (Val (Poly (_, (_, _, ee))))::_ =>
              ([Val (Poly ({prios = [](* @ pvars *), tys = tys}, (v, TForall (pvars, pcons, t),
                                                Value (PFn {pname = v,
                                                            parg = pvars,
                                                            pconst = pcons,
                                                            pcod = t,
                                                            pbody = ee}))))],
               ctx'')
            | _ => error loc "unexpected"
      end

    (* How to properly bind decs to context? And how to bind structure to signature? *)
    (* bind a module name to a sig *)
    | E.Signature (id, ds) => 
        let val (decs, context) = elabds ctx ds
        in ([], C.bindsig ctx id context)
        end

    | E.Structure (id, ds) => 
        let val (decs, context) = elabds ctx ds
        in ([], C.bindsig ctx id context)
        end
    
    | E.SigVal (s, typ) =>
        let val t = elabt ctx loc typ 
        in ([], C.bindv ctx s (mono t) (V.namedvar s))
        end

    | E.SigType (tyvars, tv) => 
          let
              val kind = length tyvars

              val tvv = V.namedvar tv

              fun conf l =
                   if length l <> kind
                   then error loc "(bug) wrong number of args to Lambda"
                   else 
                       let val nc = 
                           ListPair.foldl 
                              (fn (tv, t, ctx) =>
                               C.bindc ctx tv (Typ t) 0 Regular) 
                              ctx (tyvars, l)
                       in
                           elabt nc loc (E.TVar tv)
                       end
          in
              (* provisional instantiation of type, to make sure its
                 body is not bogus (unelaboratable) prima facie *)
              ignore ` conf (List.tabulate (kind, fn _ => new_evar ()));

              ListUtil.allpairssym op<> tyvars 
                 orelse error loc "duplicate tyvars in type dec";
              ([], C.bindc ctx tv (Lambda conf) kind Regular)
          end

    
(*
  fun elabx ctx export =
    let
      (* XXX parser should give this *)
      val loc = Pos.initposex "dummy_export"
    in
      case export of
        EL.ExportType (sl, s, NONE) => elabx ctx (EL.ExportType (sl, s, SOME (EL.TVar s)))
      | EL.ExportVal (sl, s, NONE) => elabx ctx (EL.ExportVal (sl, s, SOME (EL.Var s, loc)))

      | EL.ExportType (tys, s, SOME t) =>
          let
              
            fun checkdups atvs =
              ListUtil.alladjacent op <> `
              ListUtil.sort String.compare atvs
              orelse 
              error loc ("duplicate type vars in export type declaration (" ^ s ^ ")")

            val _ = checkdups tys
            val atys = map (fn s => (s, V.namedvar s)) tys
            val nctx = foldr (fn ((s, v), ctx) =>
                              C.bindc ctx s (Typ (TVar v)) 0 Regular) ctx atys

            val tt = elabt nctx loc t
          in
            ExportType (map #2 atys, s, tt)
          end

      | EL.ExportVal (tys, lab, SOME exp) =>
          let
            (* put type variables in context *)

            fun checkdups atvs =
              ListUtil.alladjacent op <> `
              ListUtil.sort String.compare atvs
              orelse 
              error loc ("duplicate type vars in export val declaration (" ^ lab ^ ")")

            val _ = checkdups tys

            val nctx = mktyvars ctx tys
(*
            val atys = map (fn s => (s, V.namedvar s)) tys
            val nctx = foldr (fn ((s, v), ctx) =>
                              C.bindc ctx s (Typ (TVar v)) 0 Regular) ctx atys
*)
            (* can be at any world. *)
            val w = new_wevar ()
          in

            (case elab nctx w exp of
               (Value vv, tt) =>
                 let
                   (* XXX5 should check that tyvars were all generalized *)
                   val {t = tt, tl = tp, wl = wp} = polygen ctx tt w
                 in
                   ExportVal (Poly({tys=tp, worlds=wp},
                                   (case polywgen ctx w of
                                      NONE => (lab, tt, SOME w, vv)
                                    (* XXX5 *)
                                    | SOME wv => raise Elaborate ("unimplemented: valid exportval"))))
                 end
             (* XXX: note, could hoist this binding before the exports
                with a little bit of work... *)
             | _ => error loc "expected value (not expression) in export val")
          end
    end
*)
  fun elabtd ctx (td: E.tdec) =
      case td of
          E.Dec d =>
          let val (ids, ctx) = elabd ctx d
          in
              (ids, [], ctx)
          end
        | E.Priority s => ((* print ("binding " ^ s ^ "\n"); *) ([], [], C.bindplab ctx s))
        | E.Order (s1, s2) => (([], [], C.bindpcons ctx (PConst s1, PConst s2))
                               handle C.Context s => raise (Elaborate s)
                                    | C.Absent (_, id) =>
                                      raise (Elaborate
                                                 (id ^ " in fairness criterion but not declared")))
        | E.Fairness (s, n) =>
          let val _ = (C.prio ctx s)
                      handle C.Context s => raise (Elaborate s)
                           | C.Absent (_, id) =>
                             raise (Elaborate
                                        (id ^ " in fairness criterion but not declared"))
          in
              ([], [(s, n)], ctx)
          end

  fun elabtds ctx
              (tds: E.tdec list)
      : IL.dec list * (string * intconst) list * C.context =
      List.foldl
          (fn (td, (ids, fs, ctx)) =>
              let val (ids', fs', ctx') = elabtd ctx td
              in
                  (ids @ ids', fs @ fs', ctx')
              end)
          ([], [], ctx)
          tds

  fun elaborate (EL.Prog (dl, c)) = 
    let
      (* val () = clear_mobile () *)
      val () = clear_psconstraints ()
      val () = clear_evars ()
      val G = C.bindplab Initial.initial "bot"

      val (idl, fs, G') = elabtds G dl
      val (ec, t, (pi, pp, pf)) = elabcmd G' (PSSet (PrioSet.singleton (PConst "bot"))) c

(*
      fun checkprio PConst s = s
        | checkprio _        =
          raise Elaborate ("toplevel prio dec isn't const; how did that happen?")
*)

      fun checkcons (PConst s1, PConst s2) = (s1, s2)
        | checkcons _ =
          raise Elaborate ("toplevel constraint dec isn't const; how did that happen?")

      fun solve_psetsys () = 
        let val psctx = PSContext.init_psctx (get_psevars ())
            val psctx_sol = solve_pscstrs psctx 
        in
          check_pscstrs_sol G' psctx_sol
        end
        handle PSConstraints s => raise Elaborate ("constraint solver: " ^ s)

      val prios = C.plabs G'
      val cons = List.map checkcons (C.pcons G')
    in
      print_pscstrs (); print "\n";
      solve_psetsys ();
      finalize_evars ();
      (idl, prios, cons, fs, ec)
    end handle e as Match => raise Elaborate ("match:" ^ 
                                              StringUtil.delimit " / " ` Port.exnhistory e)


end
