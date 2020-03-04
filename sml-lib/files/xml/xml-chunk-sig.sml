(* This is a simple, incorrect XML stream processor. It is designed to
   handle very large files, which fxlib has trouble with. One intended
   use is to thin large XML files, such as OpenStreetMap OSM files, to
   remove unnecessary fields and tags, in order to make it more
   efficient to store them (or possible to open them with fxlib).

   Assumes the XML is a simple (undescribed) subset of XML and valid.
   Assumes each tag or chunk of text all fits in RAM at once.
*)
signature XMLCHUNK =
sig

  (* The <?xml ...?> declaration at the beginning of each document is
     treated as text, since nobody cares about that thing and that prevents
     you from needing to deal with the possibility of a tag with ? at its
     end, which can't appear anywhere else. *)
  datatype chunk =
    Text of string
  | Tag of { startslash : bool,
             name : string,
             (* Key, quotation character, value. Value is still
                escaped, and must be compatible with the quote character,
                which must be ASCII single- or double-quote. *)
             attrs : (string * char * string) list,
             endslash : bool }

  (* Render a chunk as a string. For text, this is just the string. *)
  val chunktostring : chunk -> string

  val chunkfile : string -> chunk Stream.stream
  val chunkstring : string -> chunk Stream.stream
  val chunkstream : char Stream.stream -> chunk Stream.stream

  (* consume_file f infile

     Apply the function f to each chunk in the file, in order. *)
  val consume_file : (chunk -> unit) -> string -> unit

  (* consume_file progress f infile

     Same, but periodically call the progress function with a
     monotonically increasing number in [0, 1] giving the current
     completion rate. *)
  val consume_file_progress : (real -> unit) -> (chunk -> unit) -> string -> unit

  (* process_file f infile outfile 

     Apply the function to each chunk in the file, writing them to the
     output file. Text "" can be used to delete chunks, though it's
     the caller's prerogative to keep tags properly nested. *)
  val process_file : (chunk -> chunk) -> string -> string -> unit

  (* process_file progress f infile outfile 
     
     Same, but periodically call the progress function with a
     monotonically increasing number in [0, 1] giving the current
     completion rate. *)
  val process_file_progress : (real -> unit) -> (chunk -> chunk) -> string -> string -> unit

end