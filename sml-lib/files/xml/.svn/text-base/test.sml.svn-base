
structure Test =
struct

    val text =
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n" ^
    "<test attribute=\"Standards!\">They make programming <b>better</b>!</test>\n"

    val xml = XML.parsestring text

    val () = print (XML.tostring xml ^ "\n")

    datatype chunk = datatype XMLChunk.chunk

    fun progress r = print (Real.toString r ^ "\n")
    fun filter (Text s) = Text (StringUtil.lcase s)
      | filter (Tag { startslash, name, attrs, endslash }) =
      Tag { startslash = startslash, name = StringUtil.ucase name,
            attrs = List.filter (fn (k, _, _) => k <> "second") attrs,
            endslash = endslash }
    val () = XMLChunk.process_file_progress progress filter "test.xml" "test-out.xml"

    val () = print (StringUtil.readfile "test-out.xml")

end