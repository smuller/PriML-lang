structure XMLChunk :> XMLCHUNK =
struct

  datatype chunk =
    Text of string
  | Tag of { startslash : bool,
             name : string,
             (* Key, quotation character, value *)
             attrs : (string * char * string) list,
             endslash : bool }
  
  fun addattrs nil l = l
    | addattrs ((k, q, v) :: t) l = 
    " " :: k :: implode [#"=", q] :: v :: implode [q] :: addattrs t l

  fun chunktostring (Text s) = s
    | chunktostring (Tag { startslash, name, attrs, endslash }) =
    String.concat ((if startslash then "</" else "<") :: name ::
                   addattrs attrs [if endslash then "/>" else ">"])

  open Parsing

  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 ||

  (* Get a series of characters that are not the quote character. *)
  fun insidechars quot =
    repeat (satisfy (fn x => x <> quot)) wth implode

  val quotc = #"\"" (* " *)
  val aposc = #"'"
  val strlit =
    (literal quotc &&
     insidechars quotc <<
     literal quotc) ||
    (literal aposc &&
     insidechars aposc <<
     literal aposc)

  fun iswhitespace #" " = true
    | iswhitespace #"\n" = true
    | iswhitespace #"\r" = true
    | iswhitespace #"\t" = true
    | iswhitespace #"\v" = true
    | iswhitespace _ = false

  val whitespace = repeati (satisfy iswhitespace)
  val required_whitespace = satisfy iswhitespace >> whitespace

  (* Overly permissive! *)
  fun istagchar #"=" = false
    | istagchar #">" = false
    | istagchar #"<" = false
    | istagchar #"/" = false
    | istagchar c = not (iswhitespace c)
  val tagchars = repeat1 (satisfy istagchar) wth implode
    
  val attrkeyval =
    (tagchars << whitespace << literal #"=" << whitespace) && strlit
    wth flat3

  val attrlist = separate0 attrkeyval required_whitespace

  val tag =
    (literal #"<" >>
     opt (literal #"/")) &&
    (whitespace >>
    tagchars) &&
    (opt (required_whitespace >> attrlist)) &&
    (opt (literal #"/") <<
     literal #">")
    wth (fn (os, (tc, (al, cs))) =>
         Tag { startslash = Option.isSome os,
               name = tc,
               attrs = Option.getOpt (al, nil),
               endslash = Option.isSome cs })

  val xmlstart = explode "<?xml"
  val xmlend = explode "?>"
  val xmldecl =
    (string xmlstart >> required_whitespace >>
     attrlist <<
     string xmlend) wth (fn (attrs : (string * char * string) list) =>
                         Text (String.concat ("<?xml" :: addattrs attrs ["?>\n"])))

  (* PERF has to re-parse leading whitespace. *)
  val text = 
    whitespace >> xmldecl << whitespace ||
    repeat1 (satisfy (fn x => x <> #"<")) wth Text o implode

  val chunk = tag || text

  (* XXX these are duplicated from ../util/streamutil *)

  (* converts a string to a char stream *)
  fun stringstream s =
    let
      val ss = size s
      fun next n () =
        if n >= ss
        then Stream.empty
        else Stream.lcons (CharVector.sub(s, n),
                           next (n + 1))
    in
      Stream.old_delay (next 0)
    end


  (* convert a file to a char stream *)
  fun filestream f =
    let
      val ff = BinIO.openIn f

      fun rd () =
        case BinIO.input1 ff of
          NONE => (BinIO.closeIn ff;
                   Stream.empty)
        | SOME c => Stream.lcons(chr (Word8.toInt c), rd)
    in
      Stream.old_delay rd
    end

  fun chunkstream s =
    let val ms = Pos.markstream s
    in transform chunk ms
    end
  
  val chunkfile = chunkstream o filestream
  val chunkstring = chunkstream o stringstream

  fun consume_file_progress progress f s =
    let 

      (* Repeating filestream so that we can also check
         the file's cursor *)
      val filesize = real (OS.FileSys.fileSize s)
      val ff = BinIO.openIn s

      fun rd () =
        case BinIO.input1 ff of
          NONE => (BinIO.closeIn ff;
                   Stream.empty)
        | SOME c => Stream.lcons(chr (Word8.toInt c), rd)

      val stream = chunkstream (Stream.old_delay rd)
      (* Work around mlton bug (?) where the position calculations below
         cause it to backtrack in the stream weirdly. There may be some
         change to the way an open file is represented if we call getInstream? *)
      val _ = BinIO.getInstream ff

      fun appme (chunk : chunk) =
        let
          val pos = real (BinIO.StreamIO.filePosIn (BinIO.getInstream ff))
        in
          f chunk;
          progress (pos / filesize)
        end
    in
      Stream.app appme stream
    end

  (* Is (consume_file_progress ignore), but better to avoid trying
     to compute the file size, since that can overflow if not on a
     64-bit system *)
  fun consume_file f s = Stream.app f (chunkfile s)

  fun writestring (b : BinIO.outstream) (s : string) =
    let val v = Word8Vector.tabulate (size s, fn x => Word8.fromInt (ord (String.sub (s, x))))
    in BinIO.output (b, v)
    end

  fun process_file_mp po (f : chunk -> chunk) infile outfile =
    let
      val ff = BinIO.openOut outfile
      fun appme chunk =
        let val chunk = f chunk
          val s = chunktostring chunk
        in 
          (* print ("Write chunk [" ^ s ^ "]\n"); *)
          writestring ff s
        end
    in
      (case po of
         NONE => consume_file appme infile
       | SOME p => consume_file_progress p appme infile);
      BinIO.closeOut ff
    end

  val process_file = process_file_mp NONE
  fun process_file_progress progress = process_file_mp (SOME progress)

end
