structure Compile =
struct

exception Compile of string

type file = string

type input = file list * file

val stdlib = case OS.Process.getEnv "PRIML_LIB" of
                SOME s => s
              | NONE => (print "primlc: standard library not found: make sure PRIML_LIB environment variable is set.\n";
                        OS.Process.exit OS.Process.failure)

val basefiles = ["$(SML_LIB)/basis/basis.mlb",
                 "$(SML_LIB)/basis/mlton.mlb",
                 (* "../x/graphics.mlb", *)
                 "$(SML_LIB)/basis/schedulers/prio-private-deqs.mlb",
                 stdlib ^ "/std.sml",
                 stdlib ^ "/stdlib.sml"]

val mlton = case OS.Process.getEnv "MLTON_PARMEM" of
                SOME s => s
              | NONE => (print "primlc: mlton-parmem not found: make sure MLTON_PARMEM environment variable is set.\n";
                        OS.Process.exit OS.Process.failure)

val opts = ["-default-ann 'allowFFI true'", "-cc-opt -g"]

fun build_mlb file (deps, comp) =
    let val fs = deps @ basefiles @ [comp]
        val s = String.concatWith "\n" fs
    in
        StringUtil.writefile file s
    end

fun build_cmd mlb morefiles out opts =
    mlton ^ " " ^ (String.concatWith " " opts) ^ " -output " ^ out ^ " " ^
    mlb ^ " " ^ morefiles

fun compile inp morefiles out moreopts =
    (let val mlbname = "temp.mlb"
         val _ = build_mlb mlbname inp
         val cmd = build_cmd mlbname morefiles out (opts @ moreopts)
         val _ = print (cmd ^ "\n")
         val stat = OS.Process.system cmd
     in
         if OS.Process.isSuccess stat then
             (OS.Process.system ("rm " ^ mlbname))
         else raise (Compile "mlton-parmem returned failure")
     end)
    handle OS.SysErr (s, _) =>
           raise (Compile ("unable to run mlton-parmem: " ^ s))

end
