
structure TFCompiler =
struct
  fun eprint s = TextIO.output(TextIO.stdErr, s)

  exception TFCompiler of string

  (* Everything in this file assumes the descriptions parsed
     have been checked for duplicates, dangling types, etc. *)
  structure D = DescriptionParser

  (* TODO: Improve the way user-visible code looks. *)
  fun typetos D.Int = "int"
    | typetos D.String = "string"
    | typetos D.Bool = "bool"
    | typetos (D.List t) = postfixtypetos t ^ " list"
    | typetos (D.Option t) = postfixtypetos t ^ " option"
    | typetos (D.Tuple nil) = "unit"
    | typetos (D.Tuple ts) =
      (* n.b. "postfix" is not really correct here, but it works
         with this set of types. *)
      StringUtil.delimit " * " (map postfixtypetos ts)
    | typetos (D.Message m) = m

  (* Generate a string for the type, assuming it is in a postfixed
     position, like the argument to an option type. Also used for
     components of tuple types. *)
  and postfixtypetos (D.Tuple ts) =
      "(" ^ StringUtil.delimit " * " (map postfixtypetos ts) ^ ")"
    | postfixtypetos t = typetos t

  (* Generates the datatype declarations for the messages, which
     appear in both the signature and structure. *)
  fun gentypes l =
    let
        fun onefield (D.F { name, token, typ, hints }) =
            "    " ^ name ^ " : " ^ typetos typ

        fun one connective (D.M { name, token, fields } :: rest) =
            connective ^ " " ^ name ^ " = " ^ token ^ " of {\n" ^
            StringUtil.delimit ",\n" (map onefield fields) ^
            "\n  }\n\n" ^ one "  and" rest
          | one connective nil = ""
    in
        one "  datatype" l
    end

  (* Generate the structure declarations for the signature. *)
  fun genstructsigs l =
    let
       fun onestruct (D.M { name, token, fields }) =
         "  structure " ^ token ^ " :\n" ^
         "  sig\n" ^
         "    type t = " ^ name ^ "\n" ^
         "    val tostring : t -> string\n" ^
         "    val fromstring : string -> t\n" ^
         "    val maybefromstring : string -> t option\n" ^
         "\n" ^
         "    val tofile : string -> t -> unit\n" ^
         "    val fromfile : string -> t\n" ^
         "    val maybefromfile : string -> t option\n" ^
         "\n" ^
         "    val default : t\n" ^
         "  end\n"
    in
       StringUtil.delimit "\n" (map onestruct l)
    end

  fun genexns () =
      "  exception Parse of string\n\n"

  fun geninternal () =
      (* Internal utilities. *)
      "  structure S = Substring\n" ^
      "\n" ^
      "  fun readfile f =\n" ^
      "    let val l = TextIO.openIn f\n" ^
      "        val s = TextIO.inputAll l\n" ^
      "    in TextIO.closeIn l; s\n" ^
      "    end\n" ^
      "  fun writefile f s =\n" ^
      "   let val l = TextIO.openOut f\n" ^
      "   in  TextIO.output (l, s);\n" ^
      "       TextIO.closeOut l\n" ^
      "   end\n" ^

      (* We just need tostring and fromstring to implement the others. *)
      "  fun maybefromstringwith fs s =\n" ^
      "    (SOME (fs s)) handle Parse _ => NONE\n" ^
      "  fun fromfilewith fs f = fs (readfile f)\n" ^
      "  fun maybefromfilewith fs f =\n" ^
      "    (SOME (fs (readfile f))) handle Parse _ => NONE\n" ^
      "  fun tofilewith ts f t = writefile f (ts t)\n" ^
      "\n" ^

      (* When generating strings we use doubly-linked lists (DLL, not
         dynamically linked library :)) to concatenate strings instead
         of eagerly rebuilding the strings with ^. *)
      (* XXX not really "dll" any more, just an imperative list. *)
      "  datatype dllcell' =\n" ^
      "    D' of string * dllcell' option ref\n" ^
      (* Head of the string with the ref cell at its tail.
         the ref cell will usually be NONE unless traversing
         the internals of a dll. *)
      "  type dll' = dllcell' * dllcell' option ref\n" ^
      "  fun ^^ ((head, t as ref NONE),\n" ^
      "          (h, tail)) =\n" ^
      "    let in\n" ^
      "      t := SOME h;\n" ^
      "      (head, tail)\n" ^
      "    end\n" ^
      "   | ^^ _ =\n" ^
      "     raise Parse \"^^ bug\"\n" ^
      "  infix 2 ^^\n" ^
      "  fun $s : dll' = let val r = ref NONE in (D'(s, r), r) end\n" ^

      (* TODO Check that this CharArray stuff is portable and
         the fastest way. *)
      "  fun dlltostring (head, _) =\n" ^
      "    let\n" ^
      "      fun getsize (D' (s, r)) =\n" ^
      "        case !r of\n" ^
      "          NONE => size s\n" ^
      "        | SOME d => size s + getsize d\n" ^
      "      val a = CharArray.array(getsize head, chr 0)\n" ^
      "      fun dts (D' (s, r), idx) =\n" ^
      "        let in\n" ^
      "          CharArray.copyVec { src = s, dst = a, di = idx };\n" ^
      "          (case !r of\n" ^
      "             NONE => ()\n" ^
      "           | SOME d => dts (d, idx + size s))\n" ^
      "        end\n" ^
      "    in\n" ^
      "      dts (head, 0);\n" ^
      "      CharArray.vector a\n" ^
      "    end\n" ^

      (* Like String.concat. *)
      "  fun dllconcat' nil = $\"\"\n" ^
      "    | dllconcat' (h :: t) = h ^^ dllconcat' t\n" ^

      (* Like String.concatwith *)
      "  fun dllconcatwith' s nil = $\"\"\n" ^
      "    | dllconcatwith' s [e] = e\n" ^
      "    | dllconcatwith' s (h :: t) = h ^^ $s ^^ dllconcatwith' s t\n" ^

      (* generate a string with n spaces *)
      "  fun nspaces' n = CharVector.tabulate (n, fn _ => #\" \")\n" ^

      "  fun itos' i = if i < 0\n" ^
      "                then \"-\" ^ Int.toString (~i)\n" ^
      "                else Int.toString i\n" ^
      (* PERF Can probably be faster about this. It's pretty
         bad when the input contains lots of characters that
         need to be escaped. *)
      "  fun stos' str =\n" ^
      "    let\n" ^
      "      val digits = \"0123456789ABCDEF\"\n" ^
      "      fun hexdig i = implode [#\"\\\\\",\n" ^
      "                              CharVector.sub (digits, i div 16),\n" ^
      "                              CharVector.sub (digits, i mod 16)]\n" ^
      (* Only the double quotes and backslash truly need escaping. *)
      (* All these commented-out double quotes are to fix syntax highlighting
         both in the meta and object-level code. *)
      "      fun noescape #\"\\\"\" = false (* \" *)\n" ^ (* " *)
      "        | noescape #\"\\\\\" = false\n" ^
      "        | noescape c = ord c >= 32 andalso ord c <= 126\n" ^
      "      fun ss (s : S.substring) =\n" ^
      "        let val (clean, dirty) = S.splitl noescape s\n" ^
      "        in case S.getc dirty of\n" ^
      "              NONE => [clean, S.full \"\\\"\"] (* \" *)\n" ^ (* " *)
      "            | SOME (c, rest) =>\n" ^
      "                clean :: S.full (hexdig (ord c)) :: ss rest\n" ^
      "        end\n" ^
      "    in\n" ^
      "      S.concat (S.full \"\\\"\" :: ss (S.full str)) (* \" *)\n" ^ (* " *)
      "    end\n" ^

      (* Since we always have to be able to skip fields we don't
         know, basic parsing doesn't depend on the description.
         Start by turning it into this internal representation,
         then use the description to massage it into the concrete
         type. *)
      "  datatype fielddata' =\n" ^
      "      Int' of int\n" ^
      "    | String' of string\n" ^
      "    | List' of fielddata' list\n" ^
      "    | Message' of string * (string * fielddata') list\n" ^
      "  datatype token' =\n" ^
      "      LBRACE' | RBRACE' | LBRACK' | RBRACK'\n" ^
      "    | COMMA' | INT' of int | STRING' of string\n" ^
      "    | SYMBOL' of S.substring\n" ^
      "  type field' = string * fielddata'\n" ^

      (* Any whitespace. *)
      "  fun whitespace #\" \" = true\n" ^
      "    | whitespace #\"\\n\" = true\n" ^
      "    | whitespace #\"\\r\" = true\n" ^
      "    | whitespace #\"\\t\" = true\n" ^
      "    | whitespace _ = false\n" ^

      (* Read fields from the head of the string; return them
         and anything that remains in the string. *)
      "  fun readfields (str : S.substring) : field' list * S.substring =\n" ^
      "    let\n" ^

      "      fun isletter c = (ord c >= ord #\"a\" andalso ord c <= ord #\"z\")\n" ^
      "          orelse (ord c >= ord #\"A\" andalso ord c <= ord #\"Z\")\n" ^

      (* Digits or minus sign. *)
      "      fun numeric #\"-\" = true\n" ^
      "        | numeric c = ord c >= ord #\"0\" andalso ord c <= ord #\"9\"\n" ^

      (* Letters and digits. *)
      "      fun symbolic c = isletter c orelse\n" ^
      "        ord c >= ord #\"0\" andalso ord c <= ord #\"9\"\n" ^

      (* Read an int token. Assumes first character is - or digit. *)
      "      fun readint (s : S.substring) : token' * S.substring =\n" ^
      "        let val (f, s) = case S.sub (s, 0) of\n" ^
      "               #\"-\" => (~, S.triml 1 s)\n" ^
      (* Assume numeral. *)
      "             | _ => ((fn x => x), s)\n" ^
      "            val (intpart, rest) = S.splitl numeric s\n" ^
      "        in case Int.fromString (S.string intpart) of\n" ^
      "             NONE => raise Parse (\"Expected integer\")\n" ^
      "           | SOME i => (INT' (f i), rest)\n" ^
      "        end\n" ^

      (* Parse a symbol, assuming it starts with a letter. *)
      "      fun readsym (s : S.substring) : token' * S.substring =\n" ^
      "        let val (sympart, rest) = S.splitl symbolic s\n" ^
      "        in (SYMBOL' sympart, rest)\n" ^
      "        end\n" ^

      (* Read a string, assuming s starts with double quote *)
      "      fun readstring (str : S.substring) : token' * S.substring =\n" ^
      "        let val str = S.triml 1 str\n" ^
      "            fun stop #\"\\\"\" = false (* \" *)\n" ^ (* " *)
      "              | stop #\"\\\\\" = false\n" ^
      "              | stop c = true\n" ^
      "            fun hexvalue c =\n" ^
      "              let val oc = ord c\n" ^
      "              in  if oc >= ord #\"a\" andalso oc <= ord #\"f\"\n" ^
      "                  then 10 + (oc - ord #\"a\")\n" ^
      "                  else if oc >= ord #\"A\" andalso oc <= ord #\"F\"\n" ^
      "                  then 10 + (oc - ord #\"A\")\n" ^
      "                  else if oc >= ord #\"0\" andalso oc <= ord #\"9\"\n" ^
      "                  then (oc - ord #\"0\")\n" ^
      "                  else raise Parse \"bad escaped hex digit\"\n" ^
      "              end\n" ^
      "            fun getescape (s : S.substring) : char * S.substring =\n" ^
      "              if S.size s < 2\n" ^
      "              then raise Parse \"expected escape sequence\"\n" ^
      "              else let val c1 = S.sub (s, 0)\n" ^
      "                       val c2 = S.sub (s, 1)\n" ^
      "                       val s = S.triml 2 s\n" ^
      "                   in (chr (hexvalue c1 * 16 + hexvalue c2), s)\n" ^
      "                   end\n" ^
      "            fun de (s : S.substring) =\n" ^
      "              let val (clean, dirty) = S.splitl stop s\n" ^
      "                  val (l, rest) =\n" ^
      "                 (case S.getc dirty of\n" ^
      "                    NONE => raise Parse \"unterminated string\"\n" ^
      "                  | SOME (#\"\\\"\", rest) => (nil, rest) (* \" *)\n" ^ (* " *)
      "                  | SOME (#\"\\\\\", rest) =>\n" ^
      "                    let val (c, rest) = getescape rest\n" ^
      "                        val (ll, rest) = de rest\n" ^
      "                    in (S.full (String.implode [c]) :: ll, rest)\n" ^
      "                    end\n" ^
      "                  | _ => raise Parse \"bug: impossible dirty char\")\n" ^
      "              in (clean :: l, rest)\n" ^
      "              end\n" ^
      "          val (l, rest) = de str\n" ^
      "        in\n" ^
      "          (STRING' (Substring.concat l), rest)\n" ^
      "        end\n" ^
      (* Get the token at the head of the substring, or return NONE.
         Raises parse if a parse error is evident (like unclosed string). *)
      "      fun get_token (s : S.substring) :\n" ^
      "            (token' * S.substring) option =\n" ^
      "        let val s = S.dropl whitespace s\n" ^
      "        in if S.isEmpty s then NONE\n" ^
      "           else SOME (case S.sub (s, 0) of\n" ^
      "                  #\"}\" => (RBRACE', S.triml 1 s)\n" ^
      "                | #\"{\" => (LBRACE', S.triml 1 s)\n" ^
      "                | #\"]\" => (RBRACK', S.triml 1 s)\n" ^
      "                | #\"[\" => (LBRACK', S.triml 1 s)\n" ^
      "                | #\",\" => (COMMA',  S.triml 1 s)\n" ^
      "                | #\"\\\"\" => readstring s (* \" *)\n" ^ (* " *)
      "                | c => if isletter c\n" ^
      "                       then readsym s\n" ^
      "                       else if numeric c\n" ^
      "                       then readint s\n" ^
      "                       else raise Parse (\"Unexpected character '\" ^\n" ^
      "                                         implode [c] ^ \"'\"))\n" ^
      "        end\n" ^

      (* Get leading field data from the string, or return NONE.
         This is used recursively in contexts where there might not
         be more field data because we see a closing bracket or brace. *)
      "      fun get_data_maybe (s : S.substring) :\n" ^
      "           (fielddata' * S.substring) option =\n" ^
      "        case get_token s of\n" ^
      "           NONE => raise Parse \"Expected data\"\n" ^
      "         | SOME (INT' i, s) => SOME (Int' i, s)\n" ^
      "         | SOME (STRING' str, s) => SOME (String' str, s)\n" ^
      "         | SOME (LBRACK', s) =>\n" ^
      "           let fun eat s =\n" ^
      "                case get_data_maybe s of\n" ^
      "                   NONE => (nil, s)\n" ^
      "                 | SOME (d, s) => let val (l, s) = eat s\n" ^
      "                                  in (d :: l, s)\n" ^
      "                                  end\n" ^
      "               val (l, s) = eat s\n" ^
      "           in case get_token s of\n" ^
      "                  SOME (RBRACK', s) => SOME (List' l, s)\n" ^
      "                | _ => raise Parse \"expected closing bracket\"\n" ^
      "           end\n" ^
      "         | SOME (LBRACE', s) =>\n" ^
      "           (case get_token s of\n" ^
      "              SOME (SYMBOL' m, s) =>\n" ^
      "                let val (fs, s) = readfields s\n" ^
      "                in case get_token s of\n" ^
      "                     SOME (RBRACE', s) =>\n" ^
      "                         SOME (Message' (S.string m, fs), s)\n" ^
      "                   | _ => raise Parse \"expected rbrace after message\"\n" ^
      "                end\n" ^
      "            | _ => raise Parse \"expected symbol after lbrace\")\n" ^
      "         | SOME _ => NONE\n" ^

      (* Get field data and expect it to be present. *)
      "      fun get_data s =\n" ^
      "          case get_data_maybe s of\n" ^
      "              NONE => raise Parse \"expected field data\"\n" ^
      "            | SOME d => d\n" ^

      (* Read a single field from the head of the string. *)
      "      fun get_field (s : S.substring) : (field' * S.substring) option =\n" ^
      "        case get_token s of\n" ^
      "            NONE => NONE\n" ^
      "          | SOME (SYMBOL' tok, s) => let val (d, s) = get_data s\n" ^
      "                                     in SOME ((S.string tok, d), s)\n" ^
      "                                     end\n" ^
      (* Only other token that can come instead of a field is the closing
         brace of a nested message. Note this is reparsed, but this is very
         cheap. *)
      "          | SOME (RBRACE', _) => NONE\n" ^
      "          | SOME _ => raise Parse (\"unexpected token: \" ^ S.string s)\n" ^

      "    in\n" ^

      (* Now just get one field and recurse. *)
      "       case get_field str of\n" ^
      "           NONE => (nil, str)\n" ^
      "         | SOME (f, rest) => let val (l, rest) = readfields rest\n" ^
      "                             in (f :: l, rest)\n" ^
      "                             end\n" ^
      "    end\n" ^
      "  fun readallfields (s : string) : field' list =\n" ^
      "    let val (fs, s) = readfields (S.full s)\n" ^
      "        val s = S.dropl whitespace s\n" ^
      "    in if S.isEmpty s\n" ^
      "       then fs\n" ^
      "       else raise Parse \"Unparseable leftovers\"\n" ^
      "    end\n\n"

  fun fromfieldsname name = name ^ "_fromfields'"
  fun defaultvaluename name = name ^ "_default'"
  fun todllname name = name ^ "_todll'"

  (* Returns the ML expression (in a string) that represents the
     default value for the type. *)
  fun default_value (t : D.typ) : string =
      case t of
          D.Int => "0"
        | D.Bool => "false"
        | D.String => "\"\""
        | D.List _ => "nil"
        | D.Tuple ts => "(" ^ StringUtil.delimit "," (map default_value ts) ^ ")"
        | D.Option _ => "Option.NONE"
        | D.Message m => defaultvaluename m

  (* XXX These values may not refer to one another, which is a condition on
     the types of their fields (a forward reference to a message may only
     appear under something that ignores it when generating defaults, namely
     list or option. Currently we just let SML object to the generated code,
     but this is bad. We need to topologically sort them and reject cycles. *)
  fun gendefaults ms =
      let
          fun onefield (D.F { name, typ, ... }) =
              "    " ^ name ^ " = " ^ default_value typ
          fun onemessage (D.M { token, name, fields }) =
              "  val " ^ defaultvaluename name ^ " : " ^ name ^ " = " ^
              token ^ " {\n" ^
              StringUtil.delimit ",\n" (map onefield fields) ^
              "\n  }\n"
      in
          String.concat (map onemessage ms)
      end

  fun indent 0 = ""
    | indent n =
      if n mod 2 = 0
      then let val s = indent (n div 2) in s ^ s end
      else " " ^ indent (n - 1)

  fun gentodlls ms =
    let
      fun getmessagetoken n =
          let fun gmt (D.M { name, token, ... } :: rest) =
                     if name = n then token
                     else gmt rest
                | gmt nil =
                     raise TFCompiler ("bug? no token for message " ^ n)
          in
              gmt ms
          end

      fun onemessage _ nil = "\n"
        | onemessage connective (D.M { name, token, fields } :: rest) =
          let
              (* XXX this could shadow something we use inside tostring.
                 maybe should rename them? *)
              val pattern = "(" ^ token ^ " { " ^
                  StringUtil.delimit ", "
                     (map (fn (D.F {name, ...}) => name) fields)
                  ^ " })"

              (* XXX PERF: Don't encode stuff like NONE and nil. *)
              fun onefield (D.F { name, token, typ, hints }) =
                let
                  val isvertical = List.exists (fn D.Vertical => true) hints

                  fun furl i exp typ =
                    case typ of
                      D.Int => "$(itos' " ^ exp ^ ")"
                    | D.String => "$(stos' " ^ exp ^ ")"
                    | D.Bool => "(if " ^ exp ^ " then $\"1\" else $\"0\")"

                    | D.Tuple ts =>
                        let val fields = ListUtil.mapi
                            (fn (t, idx) =>
                             let val f = "f" ^ Int.toString idx ^ "'"
                             in (f, furl (i + 5) f t)
                             end) ts
                        in
                            "let val (" ^
                              StringUtil.delimit ", " (map #1 fields) ^
                            ") = " ^ exp ^ "\n" ^
                            indent i ^
                            "in\n" ^
                            indent (i + 2) ^
                            "$\"[\" ^^ " ^ StringUtil.delimit " ^^ $\" \" ^^ "
                                 (map #2 fields) ^
                            " ^^ $\"]\"\n" ^
                            indent i ^
                            "end"
                        end

                    | D.List t =>
                        if isvertical
                        then
                          "($\"[\\n\" ^^\n" ^
                          indent (i + 3) ^
                          "dllconcat' " ^
                          "(List.map\n" ^
                          indent (i + 3) ^
                          "(fn v => " ^
                                "$(nspaces' depth') ^^ " ^
                                furl (i + 8) "v" t ^ " ^^ $\"\\n\") " ^ exp ^ "\n" ^
                          indent i ^
                          ") ^^ $\"]\")"
                        else
                          "($\"[\" ^^\n" ^
                          indent (i + 3) ^
                          "dllconcatwith' " ^ "\" \"" ^
                          " (List.map\n" ^
                          indent (i + 3) ^
                          "(fn v => " ^ furl (i + 8) "v" t ^ ") " ^ exp ^ "\n" ^
                          indent i ^
                          ") ^^ $\"]\")"

                    | D.Option t =>
                        "(case " ^ exp ^ " of\n" ^
                        indent (i + 2) ^
                        "  SOME v => ($\"[\" ^^ " ^
                                          furl (i + 8) "v" t ^
                                          " ^^ $\"]\")\n" ^
                        indent (i + 2) ^
                        "| NONE => $\"[]\")"

                    | D.Message m =>
                        "($\"{" ^ getmessagetoken m ^
                              " \" ^^ " ^ todllname m ^
                              "(depth' + 2, " ^ exp ^ ") ^^ $\"}\")"
                in
                   "    $\"" ^ token ^ " \" ^^ " ^ furl 12 name typ
                end

          in
              connective ^
              " " ^ todllname name ^
              " (depth' : int, " ^ pattern ^ " : " ^ name ^ ") : dll' =\n" ^
              (* PERF could build space delimeter into token above *)
              StringUtil.delimit " ^^ $\" \" ^^\n"
              (map onefield fields) ^ "\n\n" ^
              onemessage "  and" rest
          end
    in
        onemessage "  fun" ms
    end

  (* Needs to be a big mutually-recursive thing to support nested
     messages. The structs just pull out their own parser. *)
  fun genfromstrings ms =
    let
        fun refname name = name ^ "_ref'"

        fun oneref (D.F { name : string, typ : D.typ, ... }) =
            "        val " ^ refname name ^ " : (" ^ typetos typ ^ ") ref =\n" ^
            "          ref (" ^ default_value typ ^ ")\n"

        (* TODO: field_got' which is a boolean flag so we can detect
           duplicates in parse. *)

        fun readfield (D.F { name, ... }) =
            "          " ^ name ^ " = !" ^ refname name

        fun getsym nil s = raise TFCompiler ("Unable to find symbol for " ^
                                             "message " ^ s ^ ".. bug?")
          | getsym (D.M { name, token, ... } :: rest) s =
            if s = name
            then token
            else getsym rest s

        (* Expect an object level variable called v in scope. It
           should contain the lightly parsed version of a value
           of the description type typ. *)
        fun makeunfurl i v typ =
            case typ of
                D.Int =>
                    "(case " ^ v ^ " of Int' i => i\n" ^
                    indent i ^
                    "  | _ => raise Parse \"expected int\")"
              | D.Bool =>
                    "(case " ^ v ^ " of Int' i => i <> 0\n" ^
                    indent i ^
                    "  | _ => raise Parse \"expected int for bool\")"
              | D.String =>
                    "(case " ^ v ^ " of String' s => s\n" ^
                    indent i ^
                    "  | _ => raise Parse \"expected string\")"
              | D.Option t =>
                    "(case " ^ v ^ " of List' nil => NONE\n" ^
                    indent i ^
                    "  | List' (d' :: _) =>\n" ^
                    indent i ^
                    "    SOME (" ^
                        makeunfurl (i + 11) "d'" t ^ ")\n" ^
                    indent i ^
                    "  | _ => raise Parse \"expected list for option\")"
              | D.List t =>
                    "(case " ^ v ^ " of List' l =>\n" ^
                    indent i ^
                    "  List.map (fn d' => " ^ makeunfurl (i + 16) "d'" t ^ ") l\n" ^
                    indent i ^
                    "  | _ => raise Parse \"expected list for list\")"
              | D.Tuple ts =>
                    let val fields = ListUtil.mapi
                        (fn (t, idx) =>
                         let val f = "f" ^ Int.toString idx ^ "'"
                         in (f, makeunfurl (i + 4) f t)
                         end) ts
                    in
                        "(case " ^ v ^ " of List' [" ^
                        StringUtil.delimit ", " (map #1 fields) ^ "] =>\n" ^
                        indent i ^
                        "  (" ^ StringUtil.delimit (",\n" ^ indent (i + 4))
                        (map #2 fields) ^ ")\n" ^
                        indent i ^
                        "  | _ => raise Parse \"expected " ^
                        Int.toString (length ts) ^ "-list for tuple\")"
                    end
              | D.Message s =>
                    "(case " ^ v ^ " of Message' "^
                      "(\"" ^ getsym ms s ^ "\", fs) => " ^
                          fromfieldsname s ^ " fs\n" ^
                    indent i ^
                    "  | _ => raise Parse \"expected submessage " ^ s ^ "\")"

        (* This is where all the magic happens, basically. After doing
           the light parsing, we loop over every field we saw in the
           parsed thing. If it's a token we recognize, we check that
           the data matches our expectations and initialize the
           ref. *)
        fun makeread connective nil =
            (* Just ignore unknown fields.
               TODO: Could collect these for round-trip compatibility
               in some future version? *)
            connective ^ "_ => ()\n"
          | makeread connective (D.F { token, name, typ, hints = _ } :: rest) =
            connective ^
            "(\"" ^ token ^ "\", d') =>\n" ^
                (* XXX check dupes. *)
            "          " ^ refname name ^ " :=\n" ^
            indent 10 ^
            makeunfurl 10 "d'" typ ^ "\n" ^
            makeread "      | " rest

        fun one _ nil = "\n"
          | one connective (D.M { name, token, fields } :: rest) =
        "\n" ^
        connective ^ " " ^ fromfieldsname name ^ " (fs : field' list) : " ^
             name ^ "=\n" ^
        "    let\n" ^
        String.concat (map oneref fields) ^
        "      fun read' d' =\n" ^
        "      case d' of\n" ^
        makeread "        " fields ^
        "    in\n" ^
        "      app read' fs;\n" ^
        (* Generate record from refs.. *)
        "      " ^ token ^ " {\n" ^
        StringUtil.delimit ",\n" (map readfield fields) ^ "\n" ^
        "        }\n" ^
        "    end\n" ^
        one "  and" rest
    in
        one "  fun" ms
    end

  fun genstructstructs l =
    let
       fun onestruct (D.M { name, token, fields }) =
         let

         in
           "\n" ^
           "  structure " ^ token ^ " =\n" ^
           "  struct\n" ^
           "    type t = " ^ name ^ "\n" ^
           "    fun tostring (m : t) : string =\n" ^
           "      dlltostring (" ^ todllname name ^ " (0, m))\n" ^

           "\n" ^
           "    fun fromstring s =\n" ^
           "      let val fs = readallfields s\n" ^
           "      in " ^ fromfieldsname name ^ " fs\n" ^
           "      end\n" ^

           "\n" ^
           "    (* derived *)\n" ^
           "    val maybefromstring = maybefromstringwith fromstring\n" ^
           "    val tofile = tofilewith tostring\n" ^
           "    val fromfile = fromfilewith fromstring\n" ^
           "    val maybefromfile = maybefromfilewith fromstring\n" ^
           "    val default = " ^ defaultvaluename name ^ "\n" ^
           "  end\n"

         end
    in
       StringUtil.delimit "\n" (map onestruct l)
    end


  fun gensig ms =
      gentypes ms ^
      genexns () ^
      genstructsigs ms

  fun genstruct ms =
      gentypes ms ^
      genexns () ^
      geninternal () ^
      gendefaults ms ^
      genfromstrings ms ^
      gentodlls ms ^
      genstructstructs ms

  fun splitext s =
      StringUtil.rfield (StringUtil.ischar #".") s

  (* TODO: in dashed-filename, generate DashedFilename *)
  (* TODO: allow the description to specify this *)
  fun capitalize s =
      case explode s of
          h :: t => if ord h >= ord #"A" andalso
                       ord h <= ord #"Z"
                    then s
                    else if ord h >= ord #"a" andalso
                            ord h <= ord #"z"
                         then implode (chr (ord h - 32) :: t)
                         else raise TFCompiler ("The filename " ^ s ^
                                                " must start with a letter," ^
                                                " since it is used to generate" ^
                                                " the structure name.")
        | _ => raise TFCompiler "The file basename may not be empty (??)"

  fun go file =
    let
        val (base, ext) = splitext file
        val s = StringUtil.readfile file
        val (D.D messages) = D.parse s

        val strname = capitalize base

        val s =
        "(* Generated from " ^ file ^ " by tfcompiler. Do not edit! *)\n\n" ^
        "structure " ^ strname ^ "TF :>\n" ^
        "sig\n" ^
        gensig messages ^
        "\nend =\n" ^
        "\n\n\n\n\n" ^
        "(* Implementation follows. You want to read tfcompiler.sml or\n" ^
        "   the README, not this generated, uncommented code. *)\n" ^
        "struct\n" ^
        genstruct messages ^
        "\nend\n"
    in
        StringUtil.writefile (base ^ "-tf.sml") s
    end


  val () = Params.main1 "Takes a single argument, the input .tfdesc file." go
  handle e =>
      let in
          eprint ("unhandled exception " ^
                  exnName e ^ ": " ^
                  exnMessage e ^ ": ");
          (case e of
               D.DescriptionParser s => eprint s
             | SimpleTok.SimpleTok s => eprint s
             | TFCompiler s => eprint s
             | _ => ());
          eprint "\nhistory:\n";
          app (fn l => eprint ("  " ^ l ^ "\n")) (Port.exnhistory e);
          eprint "\n";
          OS.Process.exit OS.Process.failure
      end

end

