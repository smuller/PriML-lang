(* Very simple optimization pass that just drops unused, non-effectful bindings. *)
structure ILUnused :> ILUNUSED =
struct

  infixr 9 `
  fun a ` b = a b

  open IL
  structure V = Variable

  exception Unused of string

  val debug = Params.flag false
      (SOME ("-debugilunused",
             "Debugging information for IL unused phase")) "debugilunused"
  fun dprint s =
    if !debug
    then print s
    else ()

(*
  no point in distinguishing between regular and valid vars here. We consider them disjoint.
  (nb. this will stop working if we switch to an AST representation of IL, which we should)

  datatype fvset = F of { var : V.Set.set,
                          uvar : V.Set.set }

  val empty = F { var = V.Set.empty, uvar = V.Set.empty }

  fun --  (s as F { var, uvar }, v) = (F { var = V.Set.delete (var, v), uvar = uvar }) handle _ => s
  fun --- (s as F { var, uvar }, v) = (F { uvar = V.Set.delete (uvar, v), var = var }) handle _ => s
  fun ++  (s as F { var, uvar }, v) = (F { var = V.Set.add (var, v), uvar = uvar })
  fun +++ (s as F { var, uvar }, v) = (F { uvar = V.Set.add (uvar, v), var = var })

  fun ??  (s as F { var, uvar }, v) = V.Set.member (var, v)
  fun ??? (s as F { var, uvar }, v) = V.Set.member (uvar, v)

  fun ||  (F { var, uvar}, F { var = var2, uvar = uvar2 }) = F { var = V.Set.union (var, var2),
                                                                 uvar = V.Set.union (uvar, uvar2) }

  fun unionl l = foldl || empty l

  infix -- --- ++ +++ ?? ??? ||
*)

  type fvset = V.Set.set
  val empty = V.Set.empty
  fun pr s =
    if !debug
    then
      let in
        print "set: ";
        V.Set.app (fn v => print (Variable.tostring v ^ " ")) s;
        print "\n"
      end
    else ()
  fun -- (s, v) =
    let in
      dprint ("Delete " ^ Variable.tostring v ^ "\n");
      V.Set.delete (s, v) handle _ => s
    end
  fun ++ (s, v) =
    let in
      dprint ("Add " ^ Variable.tostring v ^ "\n");
      V.Set.add (s, v)
    end
  fun ?? (s, v) = V.Set.member (s, v)
  fun || (s1, s2) = V.Set.union (s1, s2)
  fun unionl l = foldl || empty l
  infix -- ++ ?? ||

  fun uval value =
    case value of
      Polyvar  { var, ... } =>
        let in
          dprint ("base regvar " ^ Variable.tostring var ^ "\n");
          (empty ++ var, value)
        end
    | Polyuvar { var, ... } =>
        let in
          dprint ("base var " ^ Variable.tostring var ^ "\n");
          (empty ++ var, value)
        end
    | Int _ => (empty, value)
    | String _ => (empty, value)
    | VRecord lvl =>
        let val (l, vl) = ListPair.unzip lvl
            val (fvl, vl) = ListPair.unzip ` map uval vl
        in
          (unionl fvl, VRecord ` ListPair.zip (l, vl))
        end
    | VRoll (t, v) => let val (fv, v) = uval v
                      in
                        (fv, VRoll (t, v))
                      end
    | VInject (t, l, NONE) => (empty, value)
    | VInject (t, l, SOME v) => let val (fv, v) = uval v
                                in
                                  (fv, VInject(t, l, SOME v))
                                end
    | Sham (w, va) => let val (fv, va) = uval va
                      in
                        dprint "sham..\n";
                        (fv, Sham (w, va))
                      end
    | Fns fl =>
            let val (fv, names, fl) = ListUtil.unzip3 `
              map (fn {name, arg, dom, cod, body, inline, recu, total} =>
                   let
                     val (fv, body) = uexp body
                   in
                     (foldl (fn (v, fv) => fv -- v) fv arg,
                      name,
                      (* PERF could update 'recu' here but we don't
                         use it elsewhere.. *)
                      {name = name, arg = arg, dom = dom, cod = cod,
                       body = body, inline = inline, recu = recu,
                       total = total})
                   end) fl
                (* subtract all rec names *)
                val fvr = foldl (fn (v, fv) => fv -- v) (unionl fv) names
            in
              dprint ("fns " ^ StringUtil.delimit "/" (map (V.tostring o #name) fl));
              pr fvr;
              (fvr, Fns fl)
            end

    | Hold (w, v) => let val (fv, v) = uval v
                     in
                       (fv, Hold(w, v))
                     end

    | FSel (i, v) => let val (fv, v) = uval v
                     in (fv, FSel (i, v))
                     end

  and uexp exp =
    case exp of
      Value v => let val (fv, v) = uval v
                 in (fv, Value v)
                 end
    | App (e, el) => let val (fv1, e) = uexp e
                         val (fvs, el) = ListPair.unzip ` map uexp el
                     in
                       (fv1 || unionl fvs, App(e, el))
                     end

    | Record lvl =>
        let val (l, vl) = ListPair.unzip lvl
            val (fvl, vl) = ListPair.unzip ` map uexp vl
        in
          (unionl fvl, Record ` ListPair.zip (l, vl))
        end

    | Proj (l, t, e) =>
        let val (fv, e) = uexp e
        in
            (fv, Proj (l, t, e))
        end
    | Raise (t, e) =>
        let val (fv, e) = uexp e
        in
            (fv, Raise (t, e))
        end
    | Handle (e1, t, v, e2) =>
        let val (fv1, e1) = uexp e1
            val (fv2, e2) = uexp e2
        in
            (fv1 || (fv2 -- v), Handle (e1, t, v, e2))
        end

    (* this is no longer a binder *)
    | Say (itl, e) =>
        let val (fv, e) = uexp e
        in (fv, Say (itl, e))
        end

    | Seq (e1, e2) =>
        let val (fv1, e1) = uexp e1
            val (fv2, e2) = uexp e2
        in
            (fv1 || fv2, Seq (e1, e2))
        end

    | Tag (e1, e2) =>
        let val (fv1, e1) = uexp e1
            val (fv2, e2) = uexp e2
        in
            (fv1 || fv2, Tag (e1, e2))
        end

    | Throw (e1, e2) =>
        let val (fv1, e1) = uexp e1
            val (fv2, e2) = uexp e2
        in
            (fv1 || fv2, Throw (e1, e2))
        end

    | Unroll e =>
        let val (fv, e) = uexp e
        in (fv, Unroll e)
        end
    | Roll (t, e) =>
        let val (fv, e) = uexp e
        in (fv, Roll (t, e))
        end
    | Letcc (v, t, e) =>
        let val (fv, e) = uexp e
        in (fv -- v, Letcc(v, t, e))
        end
    | Jointext el =>
        let val (fvl, el) = ListPair.unzip ` map uexp el
        in (unionl fvl, Jointext el)
        end

    | Inject (t, l, NONE) => (empty, exp)
    | Inject (t, l, SOME e) =>
        let val (fv, e) = uexp e
        in (fv, Inject (t, l, SOME e))
        end

    | Let (d, e) =>
        let
            val (fv, e) = uexp e
        in
            case udec fv d of
                NONE => (fv, e)
              | SOME (fv, d) => (fv, Let (d, e))
        end

    | Primapp (po, el, tl) =>
        let
            val (fvl, el) = ListPair.unzip ` map uexp el
        in
            (unionl fvl, Primapp(po, el, tl))
        end

    | Get { addr, dest, typ, body } =>
        let
            val (fva, addr) = uexp addr
            val (fvb, body) = uexp body
        in
            (fva || fvb, Get { addr = addr, dest = dest, typ = typ, body = body })
        end

    | Untag { typ, obj, target, bound, yes, no } =>
        let
            val (fvo, obj) = uexp obj
            val (fvt, target) = uexp target
            val (fvy, yes) = uexp yes
            val (fvn, no) = uexp no
        in
            (fvo || fvt || (fvy -- bound) || fvn,
             Untag { typ = typ, obj = obj, target = target,
                     bound = bound, yes = yes, no = no })
        end
    | Intcase (obj, iel, def) =>
        let
          val (fvd, def) = uexp def
          val (ints, es) = ListPair.unzip iel
          val (fve, es) = ListPair.unzip ` map uexp es
          val (fvo, obj) = uexp obj
        in
          (fvd || unionl fve || fvo,
           Intcase (obj, ListPair.zip (ints, es), def))
        end
    | Sumcase (t, obj, v, lel, def) =>
        let
            val (fvd, def) = uexp def
            val (labs, es) = ListPair.unzip lel
            val (fve, es) = ListPair.unzip ` map uexp es
            val (fvo, obj) = uexp obj
        in
            (fvd || (unionl fve -- v) || fvo,
            Sumcase (t, obj, v, ListPair.zip (labs, es), def))
        end

  (* if the declaration is not needed for these fvs (below),
     then return NONE. Otherwise, return SOME (fv', d'), where
     fv' is the new free variables (above) and d' the new decl. *)
  and udec fv (Do e) = let val (fv', e) = uexp e
                       in SOME (fv || fv', Do e)
                       end
    | udec fv (d as ExternWorld _) = SOME (fv, d)
    | udec fv (d as ExternType _) =  SOME (fv, d)
                       (* XXX filter out unused imports? it changes the
                          semantics of when a program will link. *)
    | udec fv (d as ExternVal (Poly(_, (_, v, _, _)))) = SOME (fv -- v, d)
    | udec fv (d as Newtag (v, _, _)) =
                       if fv ?? v (* orelse fv ??? v always local *)
                       then SOME (fv -- v, d)
                       else NONE
    | udec fv (d as Tagtype _) = SOME(fv, d)

    (* don't care whether this is Val or Put since we're not doing type-checking *)
    | udec fv (d as Bind(b, Poly(p, (vv, t, Value va)))) =
                       (* used? *)
                       if fv ?? vv
                       then let val (fv', va) = uval va
                            in SOME ((fv -- vv) || fv', Bind(b, Poly(p, (vv, t, Value va))))
                            end
                       else
                         let in
                           print ("Drop unused polybind " ^ V.tostring vv ^ "\n");
                           NONE
                         end

    | udec fv (d as Letsham(Poly(p, (vv, t, va)))) =
                       (* used? *)
                       if fv ?? vv
                       then let val (fv', va) = uval va
                            in SOME ((fv -- vv) || fv', Letsham(Poly(p, (vv, t, va))))
                            end
                       else
                         let in
                           print ("Drop unused polyletsham " ^ V.tostring vv ^ "\n");
                           NONE
                         end

    | udec fv (d as Leta(Poly(p, (vv, t, va)))) =
                       if fv ?? vv
                       then let val (fv', va) = uval va
                            in SOME ((fv -- vv) || fv', Leta(Poly(p, (vv, t, va))))
                            end
                       else
                         let in
                           print ("Drop unused polyleta " ^ V.tostring vv ^ "\n");
                           NONE
                         end


    | udec fv (d as Bind(b, Poly(p, (vv, t, e)))) =
                           (* PERF there are other things that don't look like values
                              but that we can toss if we want. *)
                           let val (fv', e) = uexp e
                           in SOME ((fv -- vv) || fv', Bind(b, Poly(p, (vv, t, e))))
                           end

  (* given free vars needed below, generate the
     new list of decs and free vars needed above *)
  fun udecs fv nil = (fv, nil)
    | udecs fv (d :: rest) =
      let
          val (fv, rest) = udecs fv rest
      in
          case udec fv d of
              NONE => (fv, rest)
            | SOME (fv, d) => (fv, d :: rest)
      end


  fun fvexports nil = (empty, nil)
    | fvexports (ExportType (k, l, v) :: rest) =
                                       let val (fv, rest) = fvexports rest
                                       in (fv, ExportType (k, l, v) :: rest)
                                       end
    | fvexports (ExportVal (Poly(p, (l, t, wo, va))) :: rest) =
                                       let val (fv, rest) = fvexports rest
                                           val (fv2, va) = uval va
                                       in
                                         (fv || fv2, ExportVal (Poly(p, (l, t, wo, va))) :: rest)
                                       end

  fun unused (Unit (decs, exports)) =
    let
      (* exports are always all kept *)
      val (fv, exports) = fvexports exports

      val (fv, decs) = udecs fv decs
    in
      (* fv should be empty, aside from prims.. *)
      Unit (decs, exports)
    end

end
