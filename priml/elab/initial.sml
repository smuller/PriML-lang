
(* XXX5
   This needs cleanup badly; we explicate most of the initial environment now
   by making extern declarations or by using primops *)
structure Initial :> INITIAL =
struct

    open Variable
    structure P = Primop

(*
    val homename = "home"
    (* XXX address should also be in initial validity context *)
    val home = IL.WConst homename
    val homekind = IL.KJavascript
*)

    val botname = "bot"
    val bot = IL.PConst botname

    (* we (should) disallow rebinding of true, false *)

    val truename = "true"
    val falsename = "false"

    val intvar = namedvar "int"
    val ilint = IL.TVar intvar
    val charvar = namedvar "char"
    val ilchar = IL.TVar charvar
    val stringvar = namedvar "string"
    val ilstring = IL.TVar stringvar

    val ilplus = namedvar "plus"

    val ilboolsum = IL.Sum[(truename, IL.NonCarrier),
                           (falsename, IL.NonCarrier)]
    val ilbool = IL.Mu(0, [(namedvar "a", ilboolsum)])

    val ilunit = IL.TRec nil

    val eventname = "js.event"
    (* must agree with js runtime *)
    val event_dict_name = "lc_ref"

    (* XXX maybe IL.Lambda should take type and world args? *)
    val cons = 
        [("ref", IL.Lambda (IL.TRef o hd), 1, IL.Regular),
         ("cont", IL.Lambda (IL.TCont o hd), 1, IL.Regular),
         ("vector", IL.Lambda (IL.TVec o hd), 1, IL.Regular),
         (* XXX array *)
         ("int", IL.Typ ilint, 0, IL.Regular),
         ("string", IL.Typ ilstring, 0, IL.Regular),
         ("char", IL.Typ ilchar, 0, IL.Regular),
         ("unit", IL.Typ (IL.TRec nil), 0, IL.Regular)]

    val a = namedvar "alpha"
    val b = namedvar "beta"

    fun tuple l =
        let
            fun mktup _ nil = nil
              | mktup n (h::t) = (Int.toString n, h) :: mktup (n + 1) t
        in
            IL.TRec(mktup 1 l)
        end

    (* XXX reevaluate totality of these *)

    (* XXX5 should probably be done in terms of extern vals *)

    val ii = [(Variable.namedvar "_", IL.TRec [("1", ilint), ("2", ilint)])]
    val monofuns =
        [

         ("<", P.B (P.PCmp P.PLess), ii, ilbool),
         (">", P.B (P.PCmp P.PGreater), ii , ilbool),
         ("<=", P.B (P.PCmp P.PLesseq), ii, ilbool),
         (">=", P.B (P.PCmp P.PGreatereq), ii, ilbool),
         ("<>", P.B (P.PCmp P.PNeq), ii , ilbool),
         (* ("=", P.B (P.PCmp P.PEq), ii, ilbool), *)

         (* XXX floating-point stuff *)


         (*("+", P.B P.PPlus, [ilint, ilint], ilint),*)
         ("+", P.B P.PPlus, ii, ilint),
         ("-", P.B P.PMinus, ii, ilint),
         ("*", P.B P.PTimes, ii, ilint),

         ("div_", P.B P.PDiv, ii, ilint),
         (* ("mod", P.B P.PMod, [ilint, ilint], ilint), *)

         ("andb", P.B P.PAndb, ii, ilint),
         ("orb", P.B P.POrb, ii, ilint),
         ("xorb", P.B P.PXorb, ii, ilint),
         ("notb", P.PNotb, [(Variable.namedvar "_", ilint)], ilint),
         (* shift (a, b) by b mod 32. *)
         ("shl", P.B P.PShl, ii, ilint),
         ("shr", P.B P.PShr, ii, ilint)

         ]

    (* XXX, just do it inline *)
    fun mono x = IL.Poly({tys=nil}, x)
    fun quant (t, IL.Poly({tys}, x)) = IL.Poly({tys = t :: tys}, x)

      (* this is all in the standard library now... *)
    val polyfuns =
        [
	  ("=", P.PBind, quant(a, mono(IL.Arrow(true,
						[(Variable.namedvar "_", IL.TRec [("1", IL.TVar a), ("2", IL.TVar a)])], ilbool))))
	]
    (*
         (* XXX should really be exn cont, but there's no way to
            spell that type here. so make it unit cont and then the
            handler just can't use its argument. *)
         ("sethandler_", P.PSethandler, 
          mono(IL.Arrow(false, [IL.TCont ilunit], ilunit))),

         (* coercions *)
         ("ord", P.PBind, mono(IL.Arrow(true, [ilchar], ilint))),
         ("chr_", P.PBind, mono(IL.Arrow(true, [ilint], ilchar))),

         ("halt", P.PHalt, quant(a, mono(IL.Arrow(false, [ilunit], IL.TVar a)))),

         ("showval_", P.PShowval, quant(a, mono(IL.Arrow(false, [IL.TVar a], ilunit)))),


(*
         ("^", P.PJointext 2, mono(IL.Arrow(false, [ilstring, ilstring], ilstring))),

         ("!", P.PGet, quant(a, mono
                                (IL.Arrow(false, [IL.TRef (IL.TVar a)],
                                          IL.TVar a)))),

         (":=", P.PSet, quant(a, mono
                                 (IL.Arrow(false, [IL.TRef (IL.TVar a),
                                                   IL.TVar a],
                                           tuple nil)))),

         ("ref", P.PRef, quant(a, mono
                                  (IL.Arrow(false, [IL.TVar a],
                                            IL.TRef (IL.TVar a))))),
*)
(*
         ("array0", P.PArray0, quant (a, mono
                                         (IL.Arrow(true, nil, 
                                                   IL.TVec (IL.TVar a))))),

         ("vector", P.PArray, quant(a, mono 
                                      (IL.Arrow(false, [ilint, IL.TVar a],
                                                IL.TVec (IL.TVar a))))),
*)
         ("length", P.PArraylength,
            quant(a, mono
                     (IL.Arrow(true, [IL.TVec (IL.TVar a)], ilint)))),

         (* unsafe versions *)
         ("sub_", P.PSub, 
            quant(a, mono
                     (IL.Arrow(false, [IL.TVec (IL.TVar a), ilint],
                               IL.TVar a))))
(*
         ("update_", P.PUpdate, 
            quant(a, mono
                     (IL.Arrow (false, [IL.TVec (IL.TVar a),
                                        ilint,
                                        IL.TVar a],
                                tuple nil))))
*)
         ]
*)

    val vals =
        map (fn (name, prim, ty) =>
             (name, ty, IL.Primitive prim)) polyfuns @
        map (fn (name, prim, cod, dom) =>
             (name, mono (IL.Arrow(false, cod, dom)), 
              IL.Primitive prim)) monofuns

    (* there are no initial priority variables *)
    val worlds = []
    (* val initialw = foldl (fn ((id, w), ctx) => Context.bindp ctx id w) Context.empty worlds *)
    (* FIX: delete priority variables *)
    val initialw = Context.empty
    
    (* but we start with one constant, "bot" *)
    val worldlabs = [botname]
    val initialw = foldl (fn (s, ctx) => Context.bindplab ctx s) 
                                initialw worldlabs

    val initialc = foldl (fn ((s, c, k, t), ctx) =>
                          Context.bindc ctx s c k t) initialw cons

    val exnname = "exn"
    val exnvar = Variable.namedvar exnname
    val ilexn = IL.TVar exnvar

    val initialec = Context.bindc initialc exnname (IL.Typ ilexn) 0 IL.Extensible

    (* initial environment is all valid *)
    val initial = foldl (fn ((s, c, t), ctx) =>
                         Context.bindex ctx (SOME s) c (namedvar s) t)
                        initialec vals

    (* also, assume some types are mobile *)
(*
    val initial = foldr (fn (v, G) => Context.bindmobile G v) initial [intvar, charvar, stringvar]
*)

    (* XXX infix *)
    val consname = "::"
    val nilname = "nil"
    val caretname = "^"

    val matchname = "Match"

    val boolname = "bool"
    val listname = "list"

    (* Wrap an expression with declarations of things that are
       needed by elaboration, like bool and list. *)
    (* XXX5 
       this should instead be a list of default declarations,
       not an expression wrapper (for new unit-oriented
       compilation).
       the declarations of bool and list are safe,
       but the exceptions should be declared in a basis unit
       and imported here. *)
                       
    fun wrap (EL.Prog(ds, c)) =
        let val loc = Pos.initposex "prelude"
            fun %x = (x, loc)
            val decbool =
                EL.Dec (%(EL.Datatype 
                              (nil, [(boolname, 
                                      [(truename, NONE),
                                       (falsename, NONE)])])))

            val decopt =
                EL.Dec (%(EL.Datatype
                              (["'a"], [("option",
                                         [("NONE", NONE),
                                          ("SOME", SOME (EL.TVar "'a"))])])))
            val declist =
                EL.Dec (%(EL.Datatype
                              (["'a"], [("list",
                                         [("nil", NONE),
                                          ("::", SOME (EL.TRec
                                                             [("1", EL.TVar "'a"),
                                                              ("2", EL.TApp ([EL.TVar "'a"], "list"))]))])])))

            (* because parser can't parse fun inline = (x, y) = .. *)
                       (*
            val deceq =
              EL.Dec (%(EL.Fun { inline = true,
                         funs = [(["a"], "=", [([EL.PRecord[("1", EL.PVar "x"),
                                                          ("2", EL.PVar "y")]],
                                                    SOME (EL.TArrow (EL.TRec [("1", EL.TVar "a"), ("2", EL.TVar "a")], EL.TVar boolname)),
                                                    (* type ann *)
                                              %(EL.Primapp("Eq", nil, [%(EL.Var "x"),
                                                                       %(EL.Var "y")]))
                                              )])] }))
*)

(*            val dectypes =
              %(EL.ExternType(nil, eventname, SOME event_dict_name))
 *)
               
            val impexns =
              (* match ~ exn *)
              (EL.Dec (%(EL.Exception (matchname, NONE))))

        in
          EL.Prog(impexns :: decbool (* :: deceq *) :: decopt :: declist :: ds, c)
        end

    fun trueexp loc = (EL.Var (EL.Id truename), loc)
    fun falseexp loc = (EL.Var (EL.Id falsename), loc)

    val trueexpil  = IL.Roll(ilbool, IL.Inject(ilboolsum, truename,  NONE))
    val falseexpil = IL.Roll(ilbool, IL.Inject(ilboolsum, falsename, NONE))

    val truepat = EL.PApp (truename, NONE)
    val falsepat = EL.PApp (falsename, NONE)

    fun matchexp loc = (* (EL.Var matchname, loc) *)
                             (EL.App ((EL.Var (EL.Id matchname), loc),
                                (EL.Record nil, loc), false), loc)

end
