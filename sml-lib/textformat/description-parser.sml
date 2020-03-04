
(* Reads a textformat description, turning it in to the
   data structure. *)
structure DescriptionParser (* XXX sig *) =
struct

  val verbose = Params.flag false
      (SOME ("-verboseparse", "Turn on verbose parsing information, for debugging."))
      "verboseparse"

  exception DescriptionParser of string

  structure ST = SimpleTok

  datatype token =
      SYMBOL of string
    | MESSAGE
    | FIELD
    | HINT
    | VERTICAL
    | LPAREN
    | RPAREN
    | COLON
    | EQUALS
    | ASTERISK
    | LIST
    | OPTION
    | INT
    | STRING
    | BOOL

  fun toktos t =
      case t of
          SYMBOL s => "(SYM " ^ s ^ ")"
        | MESSAGE => "MESSAGE"
        | FIELD => "FIELD"
        | HINT => "HINT"
        | VERTICAL => "VERTICAL"
        | LPAREN => "LPAREN"
        | RPAREN => "RPAREN"
        | COLON => "COLON"
        | EQUALS => "EQUALS"
        | ASTERISK => "ASTERISK"
        | LIST => "LIST"
        | OPTION => "OPTION"
        | INT => "INT"
        | STRING => "STRING"
        | BOOL => "BOOL"

  val tokenizer =
      let val t = ST.empty () : token ST.tokenizer
          val t = ST.settokens t [("message", MESSAGE),
                                  ("field", FIELD),
                                  ("hint", HINT),
                                  ("vertical", VERTICAL),
                                  ("(", LPAREN),
                                  (")", RPAREN),
                                  (":", COLON),
                                  ("=", EQUALS),
                                  ("*", ASTERISK),
                                  ("list", LIST),
                                  ("int", INT),
                                  ("bool", BOOL),
                                  ("string", STRING),
                                  ("option", OPTION)]
          val t = ST.setsep t (Char.contains "()=*:")
          val t = ST.setother t SYMBOL
          val t = ST.setcomment t [ST.CSBracketed ("(*", "*)")]
      in
          ST.parser t
      end

  datatype typ =
      Int
    | String
    | Bool
    | List of typ
    | Tuple of typ list
    | Option of typ
    | Message of string

  datatype hint =
      Vertical

  datatype description =
      D of message list

  and message =
      (* TODO: explicitly retired fields *)
      (* TODO: toplevel layout hints *)
      M of { token : string, name : string, fields : field list }

  and field =
      F of { token : string, name : string, typ : typ, hints: hint list }

  local
    open Parsing
    infixr 4 << >>
    infixr 3 &&
    infix  2 -- ##
    infix  2 wth suchthat return guard when
    infixr 1 ||

    fun **(s, p) = p ##
        (fn pos => raise DescriptionParser ("@" ^ Pos.toString pos ^ ": " ^ s))
    infixr 4 **

    (* as `KEYWORD -- punt "expected KEYWORD KEYWORD2" *)
    fun punt msg _ = msg ** fail

    val ` = literal

    val symbol = maybe (fn (SYMBOL s) => SOME s | _ => NONE)

    (* Returns the function that applies the tycon *)
    fun tycon () = alt [`LIST return List,
                        `OPTION return Option]

    fun innertyp () =
        alt [`INT return Int,
             `STRING return String,
             `BOOL return Bool,
             symbol wth Message,
             (* XXX really? This is not SML syntax. *)
             `LPAREN && `RPAREN return Tuple nil,
             `LPAREN >> $tupletyp << `RPAREN]

    and postfixtyp () =
        $innertyp --
        (fn t =>
         repeat1 ($tycon) wth (fn l => foldl (fn (tyc, t) => tyc t) t l) ||
         succeed t)

    and tupletyp () =
        (* Avoid exponential parse (I think?) with left recursion *)
        $postfixtyp --
        (fn t =>
         repeat1 (`ASTERISK >> $postfixtyp) wth (fn l => Tuple (t :: l)) ||
         succeed t)

    val typ = $tupletyp

    fun hint () =
        `HINT && `VERTICAL return Vertical

    fun field () = `FIELD >>
        symbol &&
        opt (`LPAREN >> symbol << `RPAREN) &&
        (`COLON >> typ) &&
        repeat ($hint) wth
        (fn (token, (name, (typ, hints))) =>
         let val name = case name of NONE => token | SOME n => n
         in F { token = token, name = name, typ = typ, hints = hints }
         end)
        || (`FIELD --
            punt ("expected symbol [LPAREN symbol RPAREN] " ^
                  "COLON typ [HINTS] after FIELD"))

    val message = `MESSAGE >>
        symbol &&
        opt (`LPAREN >> symbol << `RPAREN) &&
        (`EQUALS >>
         repeat ($field)) wth
        (fn (token, (name, fields)) =>
         let val name = case name of NONE => token | SOME n => n
         in M { token = token, name = name, fields = fields }
         end)
      || (`MESSAGE --
          punt "expected symbol [LPAREN symbol RPAREN] EQUALS fields after MESSAGE")

  in
    val parser = repeat1 message -- (fn t => done t)
  end

  structure SM = SplayMapFn(type ord_key = string
                            val compare = String.compare)

  (* Check that there are no duplicates (message or field tokens).
     Check that any Message type refers to a message defined in this bundle.
     TODO: This can be relaxed. Field names only need to be unique within
     a message.
     TODO: Support retired fields, check that too. *)
  fun check nil = raise DescriptionParser ("Currently there must be at least " ^
                                           "one message.")
    | check (ms : message list) =
    let
        val messagenames : unit SM.map ref = ref SM.empty
        fun insertunique what (m, s) =
            case SM.find (!m, s) of
                NONE => m := SM.insert (!m, s, ())
              | SOME () =>
                    raise DescriptionParser ("Duplicate " ^ what ^
                                             ": " ^ s)

        val messagetokens : unit SM.map ref = ref SM.empty

        fun checktype Int = ()
          | checktype String = ()
          | checktype Bool = ()
          | checktype (Tuple ts) = app checktype ts
          | checktype (Option t) = checktype t
          | checktype (List t) = checktype t
          | checktype (Message m) =
            case SM.find (!messagenames, m) of
                SOME () => ()
              | NONE => raise DescriptionParser
                    ("Unknown message name " ^ m ^
                     " in type (must be defined in this description).")

        fun onefield (F { name, token, typ, hints }) =
            let
                val tokens : unit SM.map ref = ref SM.empty
                val names  : unit SM.map ref = ref SM.empty
            in
                insertunique "field token" (tokens, token);
                insertunique "field name" (names, token);
                checktype typ
            end

        fun onemessage (M { name, token, fields }) =
            let in
                insertunique "message token" (messagetokens, token);
                app onefield fields
            end
    in
        (* Get these up front because they are used for checking types.
           All other duplicate checking just happens the second time
           we see that symbol. *)
        app (fn M { name, ... } =>
             insertunique "message name" (messagenames, name)) ms;
        app onemessage ms
    end

  fun tokenize (s : string) =
    let
        val s = ST.stringstream s
        val s = Pos.markstream s
        val s = Parsing.transform tokenizer s
    in
        Stream.tolist s
    end

  fun parse (s : string) =
    let
        val s = ST.stringstream s
        val s = Pos.markstream s
        (* XXX allows and ignores untokenizable junk at end. *)
        val s = Parsing.transform tokenizer s

        val () = if !verbose
                 then let val toks = Stream.tolist s
                      in print "(verbose) Tokens:\n";
                         app (fn t => print (toktos t ^ " ")) toks
                      end
                 else ()

        (* XXX should report original file positions! *)
        val s = Pos.markany s
        val messages : message list =
            case Parsing.parse parser s of
                NONE =>
                    raise DescriptionParser "Couldn't parse a series of messages."
              | SOME ms => ms
    in
        check messages;
        D messages
    end

end
