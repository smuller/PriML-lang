structure DePrio =
struct

open EL

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
      | ECmd (p, c) =>
        (* Wrap the expression in a thunk to preserve encapsulation *)
        anonfn [PWild] (deprioc c)
      | PFn (ppats, pats, e) =>
        let val ee = deprioe e
        in
            anonfn pats ee
        end
      | PApply (e, p) => App (deprioe e, depriop loc p, false)
      | Handle (e, pes) =>
        Handle (deprioe e, List.map (fn (p, e) => (p, deprioe e)) pes),
     loc)

and depriop loc p = (Var (Id p), loc)

and deprioi ((i, loc) : inst) : exp =
    case i of
        IDo e => (* Encapsulated thread will be a thunk, so apply it. *)
        (App ((deprioe e), (Record [], loc), false), loc)
      | Spawn (p, c) => (App((App ((Var (Id "Thread.spawn"), loc),
                                  (anonfn [PWild] (deprioc c), loc), false), loc),
                            depriop loc p, false), loc)
      | Sync e => (App ((Var (Id "Thread.sync"), loc), deprioe e, false), loc)
      | Poll e => (App ((Var (Id "Thread.poll"), loc), deprioe e, false), loc)
      | Cancel e => (App ((Var (Id "Thread.cancel"), loc), deprioe e, false), loc)
      | IRet e => deprioe e

and deprioc (Cmd (sis, i): cmd) : exp =
    List.foldr
        (fn ((s, i), ee) => (Let ((Val ([], PVar s, deprioi i), #2 i), ee), #2 i))
        (deprioi i)
        sis

and depriot (t: typ) =
    case t of
        TVar _ => t
      | TApp (ts, s) => TApp (List.map depriot ts, s)
      | TRec sts => TRec (List.map (fn (s, t) => (s, depriot t)) sts)
      | TArrow (t1, t2) => TArrow (depriot t1, depriot t2)
      | TNum _ => t
      | TCmd (t, p) => TArrow (TRec [], depriot t)
      | TThread (t, p) => TApp ([depriot t], "Thread.t")
      | TForall (_, t) => depriot t

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
      | Do e => Do (deprioe e)
      | Type (ss, s, t) => Type (ss, s, depriot t)
      | Fun {inline, funs} => Fun {inline = inline, funs = List.map onefun funs}
      | WFun (s, ppats, pats, tyo, e) =>
        let val tyo = case tyo of SOME t => SOME (depriot t) | NONE => NONE
            val pvars = List.map depriopp ppats
        in
            Fun {inline = false,
                 funs = [([], s, [(pvars @ pats, tyo, deprioe e)])]}
        end
      | Datatype (ss, cs) => Datatype (ss, List.map onecon cs)
      | Tagtype _ => d
      | Newtag (s1, SOME t, s2) => Newtag (s1, SOME (depriot t), s2)
      | Newtag (s1, NONE, s2) => Newtag (s1, NONE, s2)
      | Exception (s, SOME t) => Exception (s, SOME (depriot t))
      | Exception (s, NONE) => Exception (s, NONE)
      | Structure (id, decs) => Structure (id, List.map depriod decs)
      | Signature (id, decs) => Signature (id, List.map depriod decs),
     l)

and deprioprog (Prog (tds, c)) : dec list =
    case tds of
        [] => [(Val ([], PWild, deprioc c), Pos.initpos)]
      | (Dec d)::tds' => (depriod d)::(deprioprog (Prog (tds', c)))
      | (Priority _)::tds' => deprioprog (Prog (tds', c))
      | (Order _)::tds' => deprioprog (Prog (tds', c))
      | (Fairness _)::tds' => deprioprog (Prog (tds', c))

fun priotosml l (p: string) : dec =
    (Val ([], PVar p,
          (if p = "bot" then (Var (Id "Priority.bot"), l)
           else
               (App ((Var (Id "Priority.new"), l), (Record [], l), false), l)
          )), l)

fun constosml l (s1, s2) : dec =
    (Val ([], PWild, (App ((App ((Var (Id "Priority.new_lessthan"), l),
                                 (Var (Id s1), l),
                                 false), l),
                           (Var (Id s2), l),
                           false), l)),
     l)

fun fairtosml l sns : dec list =
    let fun onefair ((s, n), sml) =
            (If ((App ((Var (Id "Priority.pe"), l),
                       (Record [("1", (Var (Id s), l)), ("2", (Var (Id "p"), l))], l),
                       false), l),
                 (Constant (CInt n), l),
                 sml),
             l)
        val catchall =
            (Constant (CInt 0w0), l)
    in
        [(Fun { inline = false,
                funs = [([], "cg__priodist",
                         [([PVar "p"], NONE, List.foldr onefair catchall sns)])]
              },
          l),
         (Val ([], PWild, (App ((Var (Id "Priority.installDist"), l),
                                (Var (Id "cg__priodist"), l),
                                false), l)),
         l)]
    end

fun deprio p prios cons fs =
    let val l = Pos.initpos
    in
        (List.map (priotosml l) prios) @
        [(Val ([], PWild, (App ((Var (Id "Basic.initPriorities"), l),
                                (Record [], l),
                                false), l)), l)] @
        (List.map (constosml l) cons) @
        (List.map (fn s => constosml l ("bot", s))
                  (List.filter (fn s => s <> "bot") prios)) @
        (List.map (fn s => constosml l (s, "(Priority.top ())")) prios) @
        [(Val ([], PWild, (App ((Var (Id "Basic.finalizePriorities"), l),
                                (Record [], l),
                                false), l)), l)] @
        (case fs of [] => [] | _ => fairtosml l fs) @
        [(Val ([], PWild, (App ((Var (Id "Basic.init"), l),
                                (Record [], l),
                                false), l)), l)] @
        (deprioprog p)
    end

end
