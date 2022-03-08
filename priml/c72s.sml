fun parse file =
    let val s = StreamUtil.ftostream file
        val ms = Pos.markstreamex file s
        val tokens = Parsing.transform Tokenize.token ms
        val parsed = Parsing.transform (Parse.prog Initfix.initial) tokens
    in
        case (Stream.tolist parsed) of
            [p] => p
          | [] => raise Parse.Parse "not a complete program"
          | _ => raise Parse.Parse "program is not a series of tdecls followed by a command"
    end

fun readlines file =
    let val s = StringUtil.readfile file
    in
        String.tokens (fn c => c = #"\n") s
    end

fun concatfiles files = 
    let val read = map readlines files
        val concattedfiles = map (String.concatWith "\n") read
        val concatted = String.concatWith "\n" concattedfiles
    in StringUtil.writefile "concatted.sml" concatted
    end

exception Input of string

val (src, output, morefiles, moreopts) =
    (case CommandLine.arguments () of
        src::output::morefiles::moreopts =>
        (src, output, morefiles, moreopts)
      | src::output::[] =>
        (src, output, "", [])
      | _ => raise (Input "primlc: usage: ./primlc source output [more files] [more options]"))
    handle Input s => (print (s ^ "\n");
                       OS.Process.exit OS.Process.failure)

val (deps, src) =
    if String.isSuffix ".mlb" src then
        let val files = readlines src
            val n = List.length files
            val srcfiles = List.filter (fn x => String.isSuffix ".prm" x) files
            val libfiles = List.filter (fn x => not (String.isSuffix ".prm" x)) files
            val _ = concatfiles srcfiles
            val (deps, src) = (libfiles, "concatted.sml")
            val _ =
                if List.length srcfiles <> 0 then ()
                else raise (Input "primlc: Main files must exist and have extension .prm")
            val _ =
                if List.all (fn s => not (String.isSuffix ".prm" s)) deps
                then ()
                else raise (Input "primlc: only one .prm file permitted")
        in
            (deps, src)
        end
    else if String.isSuffix ".prm" src then
        ([], src)
    else raise (Input "primlc: unknown file extension")

val el = parse src
        handle Parse.Parse s => (print ("Parse error: " ^ s ^ "\n");
                                 OS.Process.exit OS.Process.failure)

val el' = Nullary.nullary (Initial.wrap el)

val (idl, prios, cons, fs, il) = Elaborate.elaborate el'
                             handle Elaborate.Elaborate s =>
                                    (print ("Type error: " ^ s ^ "\n");
                                     OS.Process.exit OS.Process.failure)

val dp = DePrio.deprio el prios cons fs

val s = Layout.tostring (ELPrint.progtol dp)
        handle ELPrint.Print err => (print err; raise (ELPrint.Print err))
val () = StringUtil.writefile "temp.sml" s

val _ = Compile.compile (deps, "temp.sml") morefiles output moreopts
        handle Compile.Compile s => (print ("primlc: " ^ s ^ "\n");
                                     OS.Process.exit OS.Process.failure)
val _ = OS.Process.system ("rm temp.sml")
