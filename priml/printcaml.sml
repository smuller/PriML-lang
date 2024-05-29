structure ELPrint =
struct

  infixr 9 `
  fun a ` b = a b

    open EL
    structure L = Layout
    structure V = Variable

    val $ = L.str
    val % = L.mayAlign
    val itos = Int.toString

    exception Print of string

    fun convertid s =
	case s of
	    "SOME" => "Some"
	  | "NONE" => "None"
	  | "nil" => "[]"
	  | _ => s

    fun dolist s f i l = StringUtil.delimit s (List.map (fn m => f i m) l)

    fun escape s =
        String.translate
            (fn c => if c = #"\\" then "\\\\" else (Char.toString c))
            s

    fun listnotnone l r sep lst =
        case lst of
            [] => %[]
          | _ => %[L.listex l r sep lst]

    fun recordortuplet (layout: typ -> L.layout) sep l r osep
                      (vals : (string * typ) list) =
        let 
            val sorted = 
                ListUtil.sort (ListUtil.byfirst ML5pghUtil.labelcompare) vals
        in
            if
               (* can't be length 1 *)
               length sorted <> 1 andalso
               (* must be consecutive numbers *)
               ListUtil.alladjacent (fn ((x,_), (sx,_)) => 
                                     (case (Int.fromString x, 
                                            Int.fromString sx) of
                                          (SOME xx, SOME ssxx) => xx = ssxx - 1
                                        | _ => false)) sorted andalso
               (* must be empty or start at 1 *)
               (List.null sorted orelse
                #1 (hd sorted) = "1")
            then L.listex l r osep (map (layout o #2) sorted)
            else L.listex "{" "}" ";"
	         (map (fn (f, t) => L.seq [$(f ^ " " ^ sep ^ " "), layout t]) sorted)
        end

    fun recordortuplee (layout: exp -> L.layout) sep l r osep
                      (vals : (string * exp) list) =
        let 
            val sorted = 
                ListUtil.sort (ListUtil.byfirst ML5pghUtil.labelcompare) vals
        in
            if
               (* can't be length 1 *)
               length sorted <> 1 andalso
               (* must be consecutive numbers *)
               ListUtil.alladjacent (fn ((x,_), (sx,_)) => 
                                     (case (Int.fromString x, 
                                            Int.fromString sx) of
                                          (SOME xx, SOME ssxx) => xx = ssxx - 1
                                        | _ => false)) sorted andalso
               (* must be empty or start at 1 *)
               (List.null sorted orelse
                #1 (hd sorted) = "1")
            then L.listex l r osep (map (layout o #2) sorted)
            else L.listex "{" "}" ";"
	         (map (fn (f, t) => L.seq [$(f ^ " " ^ sep ^ " "), layout t]) sorted)
        end

    fun recordortuplep (layout: pat -> L.layout) sep l r osep
                      (vals : (string * pat) list) =
        let 
            val sorted = 
                ListUtil.sort (ListUtil.byfirst ML5pghUtil.labelcompare) vals
        in
            if
               (* can't be length 1 *)
               length sorted <> 1 andalso
               (* must be consecutive numbers *)
               ListUtil.alladjacent (fn ((x,_), (sx,_)) => 
                                     (case (Int.fromString x, 
                                            Int.fromString sx) of
                                          (SOME xx, SOME ssxx) => xx = ssxx - 1
                                        | _ => false)) sorted andalso
               (* must be empty or start at 1 *)
               (List.null sorted orelse
                #1 (hd sorted) = "1")
            then L.listex l r osep (map (layout o #2) sorted)
            else L.listex "{" "}" ";"
	         (map (fn (f, t) => L.seq [$(f ^ " " ^ sep ^ " "), layout t]) sorted)
        end

    and ttol t =
        let
        val self = ttol
      in
        (case t of
           (* should print these right-associatively *)
             TVar v => L.str v
           | TApp (ts, s) => L.paren(L.seq ((List.map self ts) @ [$s]))
           | TRec nil => $"unit"
           | TRec ltl => recordortuplet self ":" "(" ")" " *" ltl
           | TArrow (dom, cod) =>
                 L.paren (%[self dom,
                            $"->",
                            self cod])

           | TNum n => $(Int.toString n)
           | TCmd _ => raise (Print "can't print PrioML")
           | TThread _ => raise (Print "can't print PrioML")
           | TPrio _ => raise (Print "can't print PrioML"))
           (* | TForall _ => raise (Print "can't print PrioML") *)
        end

    and ctol c =
        case c of
            CInt n => $(Word32.fmt StringCvt.DEC n)
          | CString s => $("\"" ^ (escape s) ^ "\"")
          | CPrio p => $("priority[" ^ p ^ "]")
          | CChar c => $("'" ^ (Char.toString c) ^ "'")

    and pathtos p =
        case p of 
            Id s => convertid s 
          | Path (i, p) => i ^ "." ^ pathtos p

    and etol ((e, l): exp) : L.layout =
        (case e of
             Constant c => ctol c
           | Var p => $(pathtos p)
           | Float f => $(Real.toString f)
           | App (e1, e2, false) => L.paren(%[etol e1, etol e2])
           | App (e1, (Record [("1", a1), ("2", a2)], _), true) =>
             L.paren(%[etol a1, etol e1, etol a2])
           | App _ => raise (Print "ill-formed infix application")

	   | LabeledArg (l, e) =>
	     %[$("~" ^ l ^ ":"), L.paren (etol e)]

           (* print as if n-ary *)
           | Let (dd, ee) =>
                 L.paren (
                     L.align
                     [$"let",
                      L.indent 4 (dtol dd),
                      $"in",
                      L.indent 4 (etol ee)]
                 )

           | Record sel => recordortuplee etol "=" "(" ")" "," sel

           | Vector es => raise (Print "vector")

           | Proj (l, t, e) => 
                 %[L.seq[$("#" ^ l), $" ", etol e]]

           | Andalso (e1, e2) => L.paren(%[etol e1, $" && ", etol e2])
           | Orelse (e1, e2) => L.paren(%[etol e1, $" || ", etol e2])
           | Andthen (e1, e2) => raise (Print "andthen")
           | Otherwise (e1, e2) => raise (Print "otherwise")

           | If (e1, e2, e3) => L.paren(L.align [$"if ", etol e1, $" then",
                                         L.indent 4 (etol e2),
                                         $"else",
                                         L.indent 4 (etol e3)])

           | Primapp (po, ts, el) =>
                 %( [$"[PRIM", $po,
                     L.listex "(" ")" "," (map etol el)]
                   @ (case ts of 
                          nil => nil
                        | _ => [L.listex "<"">" "," (map ttol ts)])
                   @ [$"]"])

           (* also fake n-ary like above *)
           | Seq _ =>
                 let
                     fun allseqs acc (Seq (ee, er), _) = allseqs (ee::acc) er
                       | allseqs acc e = (acc, e)

                     val (front, last) = allseqs nil (e, l)
                 in
                     L.listex "(" ")" ";" (rev (map etol (last::front)))
                 end

           | Constrain (e, t) => L.paren (%[etol e, $" : ", ttol t])

           | Raise e => L.paren(%[$"raise", etol e])


           | Case ([es], ([p], e)::pes, _) =>
             L.paren(%[$"match", etol es, $"with",
                       L.indent 4 (%[ptol p, $" -> ", etol e]),
                       L.indent 2 (L.listex "" "" ""
                                            (map (fn ([p], e) =>
                                                     %[$"| ", ptol p,
                                                       $" -> ", etol e])
                                                 pes))])

           | Case _ => raise (Print "invalid case")

           | CompileWarn s => $s

           | Handle (e, (p, h)::pes) =>
             %[$"try",
	       L.paren(etol e),
               $"with",
               ptol p, $"->", etol h,
               L.listex "" "" "|"
                        (map (fn (p, e) => %[ptol p, $"->", etol e]) pes)]

           | Handle _ => raise (Print "handle with no handles?")

           | ECmd _ => raise (Print "can't print PrioML"))
           (* | PFn _ => raise (Print "can't print PrioML") *)
           (* | PApply _ => raise (Print "can't print PrioML") (* FIX: delete this *) *)

    and funtol first inline (tys, s, (ps, t, e)::[]) =
        %[$(if first then "rec " else "and "),
          $s,
          L.listex "" "" " " (map ptol ps),
          %(case t of
                NONE => []
              | SOME t => [$" : ", ttol t]),
          $" = ",
          L.indent 4 (etol e)]
      | funtol first inline (tys, s, (ps, t, e)::ptes) =
	raise (Print "multi-arm functions")

    and contol (s, sts) =
        %[$s, $" = ", L.listex "" "" " | "
                               (map (fn (s, SOME t) => %[$s, $" of ", ttol t]
                                    | (s, NONE) => $s) sts)]

    and dtol (d, _) : L.layout =
        (case d of
             Val (tys, p, e) =>
             %[listnotnone "(" ")" "," (map op$ tys),
               ptol p, $"=", etol e]
           | Do e => %[$"_ = ", etol e]
           | Type (ss, s, t) =>
             %[$"type ", listnotnone "(" ")" "," (map op$ ss), $s, $" = ", ttol t]
           | Fun {inline = inline, funs = f::funs} =>
             %[funtol true inline f,
               L.listex "" "" "\n" (map (funtol false inline) funs)]
           | Fun _ => raise (Print "function with no functions?")
           (* | WFun (s, ppats, pats, t, e) => raise (Print "can't print PrioML") (* FIX: delete this *) *)
           | Datatype (tys, cons) =>
             %[$"type ", listnotnone "(" ")" ", " (map op$ tys),
               L.listex "" "" "" (map contol cons)]
           | Tagtype s => raise (Print "tagtype")
           | Newtag _ => raise (Print "newtag")
           | Exception (new, NONE) => %[$"exception", $new]
           | Exception (new, SOME t) => %[$"exception", $new,
                                          $"of", ttol t]
	   | ExternVal _ => raise (Print "extern")
	   | ExternType _ => raise (Print "extern")
           | Structure (id, decs) => %[$"module", $id, $"=", $"struct",
             L.listex "" "" "\n" (map dtol decs), $"end"]
           | Signature (id, decs) => %[$"signature", $id, $"=", $"sig",
             L.listex "" "" "\n" (map dtol decs), $"end"]
           | SigType _ => raise (Print "does sigtype even get used?")
           | SigVal _ => raise (Print "does sigval even get used?")
        )

    and tdtol d =
	%[$"let", dtol d]
	
    and ptol p =
        case p of
            PVar s => $(convertid s)
          | PWild => $"_"
          | PAs (s, p) => L.paren (%[ptol p, $" as ", $s])
          | PRecord sps =>
            recordortuplep ptol "=" "(" ")" " ," sps
          | PConstrain (p, t) => L.paren (%[ptol p, $":", ttol t])
          | PConstant c => ctol c
	  | PApp ("::", SOME (PRecord [(_, p1), (_, p2)])) =>
	    L.paren (%[L.paren (ptol p1), $"::", L.paren(ptol p2)])
          | PApp (s, NONE) => $(convertid s)
          | PApp (s, SOME p) => L.paren (%[$(convertid s), ptol p])
          | PWhen _ => raise (Print "I don't know what a when pattern is; let's hope this doesn't come up")

    fun progtol ds =
        L.listex "" "" "\n" (map tdtol ds)
end
