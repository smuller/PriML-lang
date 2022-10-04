
structure Primop =
struct

    exception Primop of string

    datatype compare =
        PEq
      | PNeq
      | PLess
      | PLesseq
      | PGreater
      | PGreatereq

    (* nb: all operations are UNSIGNED, including comparisons
       (XXX5 actually we have not resolved this for ML5)
       *)

    (* things of int * int -> _ *)
    datatype binop =
        PTimes
      | PPlus
      | PMinus
      | PDiv
      | PMod
      | PAndb
      | PXorb
      | POrb
      | PShl
      | PShr
      | PCmp of compare

    datatype primop =
      (* primitive arithmetic stuff *)
        B of binop
      | PNeg

      (* string equality *)
      | PEqs

      | PNotb

      (* is it zero? *)
      | PNull (* two branches: yes-null/not-null *)

      (* references: can compile these as 1-length arrays *)
      | PSet
      | PGet
      | PRef

      (* string operations. strings are not arrays since
         they have more efficient native representations *)
      | PStringSub
      | PStringSubstring
      | PStringLength
      | PStringReplace
      | PIntToString

      (* coercions at EL, same as Bind at IL/CPS *)
      | POrd
      | PChr

      (* arrays and vectors use these *)
      | PArray
      | PArray0
      | PSub
      | PUpdate
      | PArraylength

      | PJointext of int

      | PPrint

      (* no-op, just bind *)
      | PBind

      (* generate an exception tag, sequentially *)
      | PNewtag

      (* XXX5 these are dead, we shot them with double barrel *)
      (* store and retrieve exception handler fn
         (these need to be relativized to the current thread) *)
      | PSethandler
      | PGethandler

      (* no run-time effect; just produces compile-time
         warning if not dead *)
      | PCompileWarn of string

      (* we need to explicitly yield for some interactions with
         the runtime. *)
      | PYield

      (* Done *)
      | PHalt

      (* DEBUGGING! *)
      | PShowval

    (* nb. jointext and compilewarn are missing *)
    val alist =
      [
      ("Times", B PTimes),
      ("Plus", B PPlus),
      ("Minus", B PMinus),
      ("Div", B PDiv),
      ("Mod", B PMod),
      ("Eq", B (PCmp PEq)),
      ("Neq", B (PCmp PNeq)),
      ("Less", B (PCmp PLess)),
      ("Lesseq", B (PCmp PLesseq)),
      ("Greater", B (PCmp PGreater)),
      ("Greatereq", B (PCmp PGreatereq)),
      ("Null", PNull),
      ("Andb", B PAndb),
      ("Xorb", B PXorb),
      ("Orb", B POrb),
      ("Shl", B PShl),
      ("Shr", B PShr),
      ("Notb", PNotb),
      ("Eqs", PEqs),
      ("Print", PPrint),
      ("Neg", PNeg),
      ("StringSub", PStringSub),
      ("StringSubstring", PStringSubstring),
      ("StringLength", PStringLength),
      ("StringReplace", PStringReplace),
      ("IntToString", PIntToString),
      ("Ord", POrd),
      ("Chr", PChr),
      ("Set", PSet),
      ("Get", PGet),
      ("Ref", PRef),
      ("Array", PArray),
      ("Array0", PArray0),
      ("Sub", PSub),
      ("Update", PUpdate),
      ("Arraylength", PArraylength),
      ("Bind", PBind),
      ("Newtag", PNewtag),
      ("Gethandler", PGethandler),
      ("Sethandler", PSethandler),
      ("Yield", PYield),
      ("Halt", PHalt),
      ("Showval", PShowval)]

    fun tostring p =
      let
        fun find nil = (case p of
                          PJointext i => ("Jointext_" ^ Int.toString i)
                        (* bad: we assume these names are short and don't have funny characters in them *)
                        (* | PCompileWarn s => ("Warn(" ^ s ^ ")") *)
                        | PCompileWarn _ => "CompileWarn"
                        | _ => raise Primop "po tostring?")
          | find ((s, p') :: rest) = if p = p'
                                     then s
                                     else find rest
      in
        find alist
      end

    (* PERF could write this whole thing out for a bit better performance, but... *)
    fun primop_cmp (p1, p2) = String.compare(tostring p1, tostring p2)

    fun fromstring s =
      case ListUtil.Alist.find op= alist s of
        NONE => if StringUtil.matchhead "Jointext_" s
                then (case Int.fromString (String.substring(s, 9, size s - 9)) of
                        SOME i => SOME (PJointext i)
                      | NONE => NONE)
                else NONE (* other special ones? *)
      | SOME po => SOME po

end
