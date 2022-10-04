
(* Combinator-style tokenizer. Takes characters as inputs, outputs
   items of type Tokens.token (see tokens.sml). This was adapted
   from a very old tokenizer for something else, so there are some
   aspects of it that are a little strange. *)

structure Tokenize :> TOKENIZE =
struct

  open Tokens

  open Parsing

  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 ||

  val quotc = #"\"" (* " *)

  fun list x = [x]

  (* Report an error with its position. *)
  (* XXX should raise exception? *)
  fun error s pos = print (Pos.toString pos ^ ": " ^ s ^ "\n")
  fun warn pos s  = print ("Warning: " ^ Pos.toString pos ^
                           ": " ^ s ^ "\n")

  (* Succeeds if p succeeds at the current point, but doesn't
     consume anything. *)

  fun ahead p = lookahead p (fn _ => succeed ())

  (* Ignores the result of p *)

  fun ignore p = p return ()

  fun midchar #"_" = true
    | midchar #"'" = true
    (* | midchar #"-" = true *)
    | midchar #"." = true
    | midchar _ = false

  val isSymbolic = Char.contains "!%&$#+-/:<=>@\\~`^|*."

  (* these never appear as part of a longer identifier *)
  val isSep = Char.contains "(),{};[] "

  fun identchar c = Char.isAlpha c orelse Char.isDigit c orelse midchar c

  (* inside text, can write backslash, then space, then newline,
     and this is treated as a non-character. *)
  fun text_line_ender () =
      (literal #"\n" return [#"\n"]) ||
      (literal #"\\" && (repeat (literal #" " ||
                                 literal #"\t")) && literal #"\n" return nil)

  (* probably should have \r, \t, \x05, etc.
     allows [brackets] because it is also used for text
     also allows an escaped literal newline to act as
     no character at all, for multi-line string constants
     with no extra spaces *)
  val escapechar =
    ((literal #"\\" >> literal quotc) ||
     (literal #"\\" >> literal #"[") ||
     (literal #"\\" >> literal #"]") ||
     (literal #"\\" >> literal #"\\") ||
     (literal #"\\" && literal #"r" return #"\r") ||
     (literal #"\\" && literal #"t" return #"\t") ||
     (literal #"\\" && literal #"n" return #"\n")) wth list
     || $text_line_ender

  val getchar = (satisfy (fn x => x <> quotc andalso x <> #"\\") wth list ||
                 escapechar)

  fun fromhex acc nil = acc
    | fromhex acc (h :: t) =
    fromhex (acc * 0w16 + (Word32.fromInt (StringUtil.hexvalue h))) t

  (* XXX overflows *)
  (* XXX get from IntConst *)
  val decimal =
    (repeat1 (satisfy Char.isDigit))
    wth (Word32.fromInt o Option.valOf o Int.fromString o implode)

  val integer =
    alt [literal #"0" >> literal #"x" >>
         (repeat1 (satisfy Char.isHexDigit))
         wth (fromhex 0w0),
         decimal]

  val insidechars = (repeat getchar) wth (implode o List.concat)

  val stringlit =
    (literal quotc) >>
    ((insidechars << (literal quotc))
      guard error "Unclosed string or bad escape.")

  val char = ((literal #"?" >> (satisfy (fn x => x <> #"\\"))) ||
              (literal #"?" >> escapechar when (fn [c] => SOME c | _ => NONE)))

  val float = ((repeat  (satisfy Char.isDigit)) <<
               (literal #".")) &&
                  (repeat1 (satisfy Char.isDigit))
                  wth (fn (a, b) =>
                       (Option.valOf (Real.fromString
                                      ("0." ^ (implode b)))) +
                       (case a of
                            nil => 0.0
                          | _ => Real.fromInt
                                (Option.valOf (Int.fromString
                                               (implode a)))))

  val number = integer || (literal #"~" >> decimal) wth op~

  fun comment () = string [#"(",#"*"]
      && (repeat ($insideComment) && string [#"*",#")"]
          guard error "Unterminated comment.")

  (* Either a nested comment or a single character (which is not
     start of a nested comment or the comment terminator). *)

  and insideComment () =
      ignore ($comment)
         || any -- (fn #"*" => ahead (satisfy (fn x => x <> #")"))
                     | #"(" => ahead (satisfy (fn x => x <> #"*"))
                     | _    => succeed ())

  (* White space. *)

  val space = repeat (ignore ($comment) || ignore (satisfy Char.isSpace))

  val keywords =
      [("and", AND),
       ("andalso", ANDALSO),
       ("andthen", ANDTHEN),

       ("cmd", CMD),
       ("spawn", SPAWN),
       ("poll", POLL),
       ("cancel", CANCEL),
       ("sync", SYNC),
       ("ret", RET),
       ("priority", PRIORITY),
       ("order", ORDER),
       ("fairness", FAIRNESS),
(*        ("wfun", WFUN), *)
       ("[", LSQUARE),
       ("]", RSQUARE),
       ("<-", LARROW),
       ("<", LESSTHAN),
       ("<=", LESSEQUAL),
       ("cand", CAND),
       ("main", MAIN),
       ("thread", THREAD),
       ("forall", FORALL),

       ("as", AS),
       ("case", CASE),
       ("datatype", DATATYPE),
       ("import", IMPORT),
       ("do", DO),
       ("datafile", DATAFILE),
       ("else", ELSE),
       ("end", END),
       ("exception", EXCEPTION),
       ("vexception", VEXCEPTION),
       ("fn", FN),
       ("fun", FUN),
       ("handle", HANDLE),
       ("if", IF),
       ("in", IN),
       ("infix", INFIX),
       ("infixr", INFIXR),
       ("let", LET),
       ("lib", LIB),
       ("library", LIBRARY),
       ("newtag", NEWTAG),
       ("newvtag", NEWVTAG),
       ("nonfix", NONFIX),
       ("of", OF),
       ("op", OP),
       ("orelse", ORELSE),
       ("otherwise", OTHERWISE),
       ("primapp", PRIMAPP),
       ("inline", INLINE),
       ("sig", SIG),
       ("signature", SIGNATURE),
       ("deriving", DERIVING),
       ("open", OPEN),
       ("tagtype", TAGTYPE),
       ("then", THEN),
       ("type", TYPE),
       ("val", VAL),
       ("raise", RAISE),
       ("unit", UNIT),
       ("(", LPAREN),
       (")", RPAREN),
       ("{", LBRACE),
       ("}", RBRACE),
       ("->", ARROW),
       (",", COMMA),
       (".", DOT),
       ("*", TIMES),
       ("/", DIVIDE),
       ("#", HASH),
       ("|", BAR),
       ("_", UNDERSCORE),
       (":", COLON),
       (";", SEMICOLON),
       ("=", EQUALS),
       ("=>", DARROW)
       ]

  (* PERF could use hash table or other sub-linear search structure *)
  fun ident s =
      let
          fun id nil = ID s
            | id ((a,b)::t) = if a = s then b else id t
      in
          id keywords
      end

  val letters = (satisfy Char.isAlpha || literal #"'") &&
                repeat (satisfy identchar) wth op::

  val word =
      alt [letters wth implode,
           (satisfy isSep) wth Char.toString,
           repeat1 (satisfy isSymbolic) wth implode]

  fun goodtoken () = space >> !! (alt [char wth CHAR,
                                       float wth FLOAT,
                                       number wth INT,
                                       stringlit wth (fn s => STR s),
                                       word wth ident,
                                       (* XXX why isn't this
                                          covered by ident above? *)
                                       literal #"_" return UNDERSCORE
                                       ])


  (* a list of text characters starting from column 'col'.
     after a newline, we consume whitespace to line up with
     the start column. *)
  and indented_textchars col =
    let in
      (* print ("i_t " ^ Int.toString col ^ "\n"); *)
    alt
    [satisfy (fn x => x <> #"]" andalso x <> #"\\" andalso x <> #"["
                                andalso x <> #"\n") wth list,

     $text_line_ender && $ (skipwhites col col) wth op @,
     escapechar]
    end

  (* skip 'col' whitespace characters, but if we see something else,
     emit a warning; set indentation to 0, and try to salvage the
     text. *)
  and skipwhites orig 0 () = succeed nil
    | skipwhites orig n () =
    let in
      (* print ("skipwhites " ^ Int.toString orig ^ " " ^ Int.toString n ^ "\n"); *)
    alt [(* actual whitespace *)
         literal #" " >> $(skipwhites orig (n - 1)),
         (* if we see newline, include it but start over. *)
         $text_line_ender && $(skipwhites orig orig) wth op@,
         (* tab characters are bad news; XXX use parameter
            to define their size? (and then don't warn?)
            nb. have to agree with Pos's idea of tab length *)
         literal #"\t" -- (fn _ =>
                           get
                           (fn pos =>
                            let in
                              warn pos "tab character in text indentation";
                              if (n >= 8)
                              then $(skipwhites orig (n - 8))
                              else succeed (List.tabulate(8 - n,
                                                          fn _ => #" "))
                            end)),
         get (fn pos =>
              let in
                warn pos "non-space character in text indentation";
                succeed nil
              end)]
    end

  val token =
      alt [$goodtoken,
           !! (space >> any wth BAD)]

end
