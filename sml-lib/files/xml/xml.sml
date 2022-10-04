(* Simplified interface for reading non-enormous XML documents into
   a datatype.
   Tom Murphy VII, 2009.
   This file only: Use and distribute freely.
*)

structure XML :> XML =
struct

  exception XML of string

  type attribute = string * string
  type tag = string * attribute list

  datatype tree =
      Text of string
    | Elem of tag * tree list

  val dtd = Dtd.initDtdTables()

  fun vectortoutf8 v =
      let
          val BUFFER_SIZE = 1024

          fun write ((s, arr, sz), w) =
              let in
                  CharArray.update(arr, sz, chr (Word8.toInt w));
                  (s, arr, sz + 1)
              end handle Subscript =>
                  write ((CharArraySlice.vector
                            (CharArraySlice.slice(arr, 0, NONE)) :: s,
                          arr, 0), w)

          fun finalize (s, arr, sz) =
              String.concat(rev (CharArraySlice.vector
                                 (CharArraySlice.slice(arr, 0, SOME sz)) :: s))

          val start = (nil, CharArray.array(BUFFER_SIZE, chr 0), 0)

          val finish = Vector.foldl (EncodeUTF8.writeCharUtf8 write) start v
      in
          finalize finish
      end

  (* PERF *)
  fun datatoutf8 l = vectortoutf8 (Vector.fromList l)

  (* XXX Don't know what most of these are... *)
  fun getvalue (a : Base.AttValue) =
      case a of
      Base.AV_CDATA (u : UniChar.Vector) => raise XML "Unimplemented AV_CDATA"
    | Base.AV_NMTOKEN (u : UniChar.Data) => raise XML "Unimplemented AV_NMTOKEN"
    | Base.AV_NMTOKENS (ul : UniChar.Data list) => raise XML "Unimplemented AV_NMTOKENS"
    | Base.AV_ID (i : int) => raise XML "Unimplemented AV_ID"
    | Base.AV_IDREF (i : int) => raise XML "Unimplemented AV_IDREF"
    | Base.AV_IDREFS (il : int list) => raise XML "Unimplemented AV_IDREFS"
    | Base.AV_ENTITY (i : int) => raise XML "Unimplemented AV_ENTITY"
    | Base.AV_ENTITIES (il : int list) => raise XML "Unimplemented AV_ENTITIES"
    | Base.AV_GROUP (il : int list, i : int) => raise XML "Unimplemented AV_GROUP"
    | Base.AV_NOTATION (il : int list, i : int) => raise XML "Unimplemented AV_NOTATION"

  fun spectoattr (i : int, ap : HookData.AttPresent,
                  (* This is the text before the attribute name
                     and between the attribute and value (I think),
                     which is useless except for unparsing *)
                  uo : (UniChar.Data * UniChar.Data) option) =
      (datatoutf8 (Dtd.Index2AttNot dtd i),
       case ap of
           (* XXX ??? *)
           HookData.AP_IMPLIED => "IMPLIED"
         | HookData.AP_MISSING => "MISSING"
         | HookData.AP_DEFAULT (_, v2, ao) => vectortoutf8 v2
         | HookData.AP_PRESENT (_, v2, ao) => vectortoutf8 v2)

  structure Hooks =
  struct
      open IgnoreHooks


      type AppData = tree list * (tag * tree list) list
      type AppFinal = tree

      val appstart = (nil, nil)

      fun hookStartTag ((content, stack),
                        (_ (* dtd *), id, atts, _, empty)) =
          let val t = datatoutf8 (Dtd.Index2Element dtd id)
          in
              if empty
              then (Elem ((t, map spectoattr atts), nil) :: content, stack)
              else (nil, ((t, map spectoattr atts), content) :: stack)
          end

      fun hookEndTag ((_, nil), _) = raise XML "ill-formed: no tag open"
        | hookEndTag ((content, (tag, content') :: stack), _) =
          (Elem (tag, rev content) :: content', stack)

      fun hookData ((content, stack), (_, vec, _)) =
          let in
              (*
              print "hookData:\n  ";
              Vector.app (fn uc =>
                          print (UniChar.Char2String uc ^ "(" ^ Word.toString uc ^ ")")
                          ) vec;
              print "\nend hookData\n";
              *)
              (Text (vectortoutf8 vec) :: content, stack)
          end

      fun hookCData ((content, stack), (_, vec)) =
          (Text (vectortoutf8 vec) :: content, stack)

      fun hookCharRef ((content, stack), (_, c, _)) =
          (Text (datatoutf8 [c]) :: content, stack)

      fun hookFinish ([tree], nil) = tree
        | hookFinish (nil, _) = raise XML "ill-formed: parsed zero trees"
        | hookFinish _ = raise XML "ill-formed: multiple trees?"
  end

  structure Opt = ParserOptions ()
  (* Turn off validation. Almost universally the DTD is given via a URL,
     and fetching that is not easy to support and doesn't give much
     benefit. If validation is on, then basically all attributes will
     be rejected as errors, because they are undeclared. *)
  val () = Opt.O_VALIDATE := false
  structure Parser = Parse(structure Dtd = Dtd
                           structure Hooks = Hooks
                           structure ParserOptions = Opt
                           structure Resolve = ResolveNull)

  fun normalize (Elem(tag, tl)) =
      let
          fun make s (Text "" :: rest) = make s rest
            | make s (Text t :: rest) = make (t :: s) rest
            | make nil ((e as Elem _) :: rest) = normalize e :: make nil rest
            | make l ((e as Elem _) :: rest) =
                Text (String.concat (rev l)) :: normalize e :: make nil rest
            | make nil nil = nil
            | make l nil = [Text (String.concat (rev l))]
      in
          Elem(tag, make nil tl)
      end
    | normalize e = e

  fun parsefile file =
      normalize(Parser.parseDocument
                (SOME (Uri.String2Uri file)) (SOME dtd) Hooks.appstart)

  fun parsestring string =
      normalize (Parser.parseDocument
                 (SOME (Uri.rawUri string))
                 (SOME dtd) Hooks.appstart)

  fun getleaves tree =
      let
          val alist = ref nil
          fun alist_insert (k, v) =
              let
                  fun r nil = [(k, [v])]
                    | r ((k', vs) :: t) = if k = k'
                                          then (k', v :: vs) :: t
                                          else (k', vs) :: r t
              in
                  alist := r (!alist)
              end

          fun process (Elem((tag, attrs_ignored), [Text text])) =
              alist_insert (tag, text)
            | process (Elem((tag, attrs_ignored), nil)) = alist_insert (tag, "")
            | process (e as Text _) = ()
            | process (Elem(t, tl)) = app process tl

      in
          process tree;
          (* We accumulated it backwards, so undo that *)
          rev (map (fn (k, vs) => (k, rev vs)) (!alist))
      end

  fun getattr nil _ = NONE
    | getattr ((s, v) :: rest) ss = if s = ss
                                    then SOME v
                                    else getattr rest ss

  (* Written imperatively to avoid n^2 performance for big documents. *)
  fun tostring tree =
      let
          val BUFFER_SIZE = 1024

          val buf = ref (nil, CharArray.array(BUFFER_SIZE, chr 0), 0)

          fun write w =
              let val (s, arr, sz) = !buf
              in
                  let in
                      CharArray.update(arr, sz, w);
                      buf := (s, arr, sz + 1)
                  end handle Subscript =>
                      (buf := (CharArraySlice.vector
                               (CharArraySlice.slice(arr, 0, NONE)) :: s,
                               arr, 0);
                       write w)
              end
          fun writes s = CharVector.app write s

          fun finalize (s, arr, sz) =
              String.concat(rev (CharArraySlice.vector
                                 (CharArraySlice.slice(arr, 0, SOME sz)) :: s))

          (* FIXME This is wrong; it needs to escape embedded <> " etc. *)
          fun tos (Elem ((tag, attrs), tl)) =
              let
                  fun oneattr (k, v) =
                      let in
                          write #" ";
                          writes k;
                          writes "=\""; (* " *)
                          writes v;
                          write #"\"" (* " *)
                      end
              in
                  write #"<";
                  writes tag;
                  app oneattr attrs;
                  write #">";
                  app tos tl;
                  writes "</";
                  writes tag;
                  write #">"
              end
            | tos (Text s) = writes s
      in
          tos tree;
          finalize (!buf)
      end

end
