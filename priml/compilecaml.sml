structure CompileCaml =
struct

exception Compile of string

type file = string

type input = file list * file

val ocamlc = case OS.Process.getEnv "OCAMLC" of
                SOME s => s
              | NONE => (print "primlc: ocamlc not found: make sure OCAMLC environment variable is set.\n";
                        OS.Process.exit OS.Process.failure)

val opts = []


fun build_cmd out src morefiles packages opts =
    "ocamlfind " ^ ocamlc ^ " "
    ^ (String.concatWith " " opts) ^ " "
    ^ " -o " ^ out
    ^ " -linkpkg -thread -package " ^ (String.concatWith " " packages)
    ^ " " ^ morefiles
    ^ " " ^ src

fun compile inp packages morefiles out moreopts =
    (let val packages = "domainslib"::packages
	 val cmd = build_cmd out inp morefiles packages (opts @ moreopts)
         val _ = print (cmd ^ "\n")
         val stat = OS.Process.system cmd
     in
         if OS.Process.isSuccess stat then ()
(*             (OS.Process.system ("rm " ^ inp)) *)
         else raise (Compile "ocamlfind returned failure")
     end)
    handle OS.SysErr (s, _) =>
           raise (Compile ("unable to run ocamlfind: " ^ s))

end
