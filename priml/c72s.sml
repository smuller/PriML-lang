fun withtimer f =
    let val timer = Timer.startRealTimer ()
	val result = f ()
	val endtime = Timer.checkRealTimer timer
    in
	(result, endtime)
    end
	

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

exception Input of string

val (src, output, morefiles, moreopts) =
    (case CommandLine.arguments () of
        src::output::morefiles =>
        (src, output, String.concatWith " " morefiles, [])
      | src::output::[] =>
        (src, output, "", [])
      | _ => raise (Input "primlc: usage: ./primlc source output [more files] [more options]"))
    handle Input s => (print (s ^ "\n");
                       OS.Process.exit OS.Process.failure)

val (deps, src) =
    (if String.isSuffix ".mlb" src then
        let val files = readlines src
            val n = List.length files
            val (deps, src) = (List.take (files, n - 1), List.last files)
            val _ =
                if String.isSuffix ".prm" src then ()
                else raise (Input "primlc: Main file must have extension .prm")
            val _ =
                if List.all (fn s => not (String.isSuffix ".prm" s)) deps
                then ()
                else raise (Input "primlc: only one .prm file permitted")
        in
            (deps, src)
        end
    else if String.isSuffix ".prm" src then
        ([], src)
    else raise (Input "primlc: unknown file extension"))
    handle Input s => (print (s ^ "\n");
		       OS.Process.exit OS.Process.failure)
	       
val ((el, el'), parse_time) =
    withtimer
	(fn () =>
	    let
		val el = parse src
			 handle Parse.Parse s => (print ("Parse error: " ^ s ^ "\n");
						  OS.Process.exit OS.Process.failure)
	    in
		(el, Nullary.nullary (Initial.wrap el))
	    end)

val ((idl, prios, cons, fs, il), hm_time) =
    withtimer (fn () => Elaborate.elaborate el'
                             handle Elaborate.Elaborate s =>
                                    (print ("Type error: " ^ s ^ "\n");
                                     OS.Process.exit OS.Process.failure))

val (pscons, constraint_time) =
    withtimer (fn () => Constraint.consprog (idl, prios, cons, fs, il))

val (_, solve_time) =
    withtimer
	(fn () => Solve.solve_psetcstrs pscons (* (List.map PSetCstrs.dosub_cstr pscons) *)
	handle PSetCstrs.PSConstraints s =>
	       (print s;
		OS.Process.exit OS.Process.failure))

val (_, gen_time) =
    withtimer
	(fn () =>
	    let
		val dp = DePrio.deprio el prios cons fs

		val s = Layout.tostring (ELPrint.progtol dp)
			handle ELPrint.Print err => (print err; raise (ELPrint.Print err))
	    in
		StringUtil.writefile "temp.ml" s
	    end)
					      
val (_, ocaml_time) =
    withtimer
	(fn () => CompileCaml.compile "temp.ml" [] morefiles output moreopts
		   handle CompileCaml.Compile s => (print ("primlc: " ^ s ^ "\n");
						    OS.Process.exit OS.Process.failure)
	)

(* val _ = OS.Process.system ("rm temp.ml") *)

val _ = print ("Parse and Desugar Time (us): \t"
	       ^ (LargeInt.toString (Time.toMicroseconds parse_time))
	       ^ "\n")
val _ = print ("Hindley-Milner Time (us): \t"
	       ^ (LargeInt.toString (Time.toMicroseconds hm_time))
	       ^ "\n")
val _ = print ("Constraint Gen Time (us): \t"
	       ^ (LargeInt.toString (Time.toMicroseconds constraint_time))
	       ^ "\n")
val _ = print ("Constraint Solve Time (us): \t"
	       ^ (LargeInt.toString (Time.toMicroseconds solve_time))
	       ^ "\n")
val _ = print ("Number of Constraints: \t\t"
	       ^ (Int.toString (List.length pscons))
	       ^ "\n")
val _ = print ("OCaml Generation Time (us): \t"
	       ^ (LargeInt.toString (Time.toMicroseconds gen_time))
	       ^ "\n")
val _ = print ("OCaml Compilation Time (us): \t"
	       ^ (LargeInt.toString (Time.toMicroseconds ocaml_time))
	       ^ "\n")
