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
            else L.recordex sep (ListUtil.mapsecond layout sorted)
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
            else L.recordex sep (ListUtil.mapsecond layout sorted)
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
            else L.recordex sep (ListUtil.mapsecond layout sorted)
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
           | TForall _ => raise (Print "can't print PrioML"))
        end

    and ctol c =
        case c of
            CInt n => $(Word32.fmt StringCvt.DEC n)
          | CString s => $("\"" ^ (escape s) ^ "\"")
          | CChar c => $("#\"" ^ (Char.toString c) ^ "\"")

    and pathtos p =
        case p of 
            Id s => s 
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

           (* print as if n-ary *)
           | Let (dd, ee) =>
                 L.paren (let
                     fun alldecs acc (Let (dd, er), _) = alldecs (dd::acc) er
                       | alldecs acc e = (acc, e)

                     val (decs', body) = alldecs nil (e, l)
                     val decs = rev (map dtol decs')
                 in
                     L.align
                     [$"let",
                      L.indent 4 (L.align decs),
                      $"in",
                      L.indent 4 (etol body),
                      $"end"]
                 end)

           | Record sel => recordortuplee etol "=" "(" ")" "," sel

           | Vector es => L.listex "{" "}" "," (map etol es)

           | Proj (l, t, e) => 
                 %[L.seq[$("#" ^ l), $" ", etol e]]

           | Andalso (e1, e2) => L.paren(%[etol e1, $" andalso ", etol e2])
           | Orelse (e1, e2) => L.paren(%[etol e1, $" orelse ", etol e2])
           | Andthen (e1, e2) => L.paren(%[etol e1, $" andthen ", etol e2])
           | Otherwise (e1, e2) => L.paren(%[etol e1, $" otherwise ", etol e2])

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
             L.paren(%[$"case", etol es, $"of",
                       L.indent 4 (%[ptol p, $" => ", etol e]),
                       L.indent 2 (L.listex "" "" ""
                                            (map (fn ([p], e) =>
                                                     %[$"| ", ptol p,
                                                       $" => ", etol e])
                                                 pes))])

           | Case _ => raise (Print "invalid case")

           | CompileWarn s => $s

           | Handle (e, (p, h)::pes) =>
             %[L.paren(etol e),
               $"handle",
               ptol p, $"=>", etol h,
               L.listex "" "" "|"
                        (map (fn (p, e) => %[ptol p, $"=>", etol e]) pes)]

           | Handle _ => raise (Print "handle with no handles?")

           | ECmd _ => raise (Print "can't print PrioML")
           | PFn _ => raise (Print "can't print PrioML")
           | PApply _ => raise (Print "can't print PrioML"))

    and funtol first inline (tys, s, (ps, t, e)::ptes) =
        %[$(if first then "fun " else "and "),
          %[listnotnone "(" ")" ", " (map op$ tys)],
          $(if inline then "inline " else ""), $s,
          L.listex "" "" " " (map ptol ps),
          %(case t of
                NONE => []
              | SOME t => [$" : ", ttol t]),
          $" = ",
          L.indent 4 (etol e),
          L.indent 2 (
              L.listex "" "" "\n"
                       (map (fn (ps, t, e) =>
                                %[$"|", $s,
                                  L.listex "" "" " " (map ptol ps),
                                  %(case t of
                                        NONE => []
                                      | SOME t => [$":", ttol t]),
                                  $"=",
                                  L.indent 4 (etol e)]) ptes)
          )]

    and contol (s, sts) =
        %[$s, $" = ", L.listex "" "" " | "
                               (map (fn (s, SOME t) => %[$s, $" of ", ttol t]
                                    | (s, NONE) => $s) sts)]

    and dtol (d, _) =
        (case d of
             Val (tys, p, e) =>
             %[$"val", listnotnone "(" ")" "," (map op$ tys),
               ptol p, $"=", etol e]
           | Do e => %[$"do", etol e]
           | Type (ss, s, t) =>
             %[$"type ", listnotnone "(" ")" "," (map op$ ss), $s, $" = ", ttol t]
           | Fun {inline = inline, funs = f::funs} =>
             %[funtol true inline f,
               L.listex "" "" "\n" (map (funtol false inline) funs)]
           | Fun _ => raise (Print "function with no functions?")
           | WFun (s, ppats, pats, t, e) => raise (Print "can't print PrioML")
           | Datatype (tys, cons) =>
             %[$"datatype ", listnotnone "(" ")" ", " (map op$ tys),
               L.listex "" "" "" (map contol cons)]
           | Tagtype s => %[$"tagtype", $s]
           | Newtag (new, NONE, ext) => %[$"newtag", $new, $"in", $ext]
           | Newtag (new, SOME t, ext) => %[$"newtag", $new,
                                       $"tags", ttol t, $"in",
                                       $ext]
           | Exception (new, NONE) => %[$"exception", $new]
           | Exception (new, SOME t) => %[$"exception", $new,
                                          $"of", ttol t]
           | Structure (id, decs) => %[$"structure", $id, $"=", $"struct",
             L.listex "" "" "\n" (map dtol decs), $"end"]
           | Signature (id, decs) => %[$"signature", $id, $"=", $"sig",
             L.listex "" "" "\n" (map dtol decs), $"end"]
           | SigType _ => raise (Print "does sigtype even get used?")
           | SigVal _ => raise (Print "does sigval even get used?")
        )
    and ptol p =
        case p of
            PVar s => $s
          | PWild => $"_"
          | PAs (s, p) => L.paren (%[$s, $" as ", ptol p])
          | PRecord sps =>
            recordortuplep ptol "=" "(" ")" " ," sps
          | PConstrain (p, t) => L.paren (%[ptol p, $":", ttol t])
          | PConstant c => ctol c
          | PApp (s, NONE) => $s
          | PApp (s, SOME p) => L.paren (%[$s, ptol p])
          | PWhen _ => raise (Print "I don't know what a when pattern is; let's hope this doesn't come up")

    fun progtol ds =
        L.listex "" "" "\n" (map dtol ds)
end
