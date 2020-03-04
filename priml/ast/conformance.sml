(* Tests that the ASTFn works correctly. *)
(* XXX This is far from complete! One AST implementation passed
   this but then looped forever when compiling some programs.

   another bug that slipped through: substitution inversion
   in the lambda case ignored the possibility that the bound
   variable would incur capture. passed conformance, died in
   directcall EBETA phase.
 *)

structure ASTConformance =
struct

  exception Conformance of string

  structure Arg =
  struct
    val ctr = ref 0
    type var = string
    val var_eq = op= : string * string -> bool
    val var_cmp = String.compare
    fun var_vary s = 
      let in
        ctr := !ctr + 1;
        s ^ "_" ^ Int.toString (!ctr)
      end

    fun var_tostring s = s

    val Exn = Conformance

    type leaf = string
    val leaf_cmp = String.compare
  end

  structure A = ASTFn(Arg)
  open A
  infixr / \ // \\

  fun ttos t =
    case look t of
      $ l => "\"" ^ String.toString l ^ "\""
    | V v => v
    | x \ y => "(" ^ x ^ " \\ " ^ ttos y ^ ")"
    | x / y => "(" ^ ttos x ^ " / " ^ ttos y ^ ")"
    | S l => "[" ^ StringUtil.delimit "," (map ttos l) ^ "]"
    | B (xs, t) => "{" ^ StringUtil.delimit "," xs ^ ". " ^ ttos t ^ "}"


  fun real_count x a =
    case look a of
      V y => if x = y then 1 else 0
    | l / r => real_count x l + real_count x r
    | _ \ r => real_count x r
    | S l => foldr op+ 0 (map (real_count x) l)
    | B (_, r) => real_count x r
    | $ _ => 0


  fun show ast = Layout.print(layout ast, print);

  fun fail ast msg =
    let in
      print "AST:\n";
      show ast;
      print "\n";
      raise Conformance msg
    end

  fun correct_count l t =
    app (fn x =>
         let val rc = real_count x t
             val c = count t x
         in
           if rc = c
           then ()
           else fail t ("count not correct for " ^ x ^ " (got " ^ 
                        Int.toString c ^ " wanted " ^ Int.toString rc ^ 
                        ") in: " ^ ttos t)
         end) l

  fun free_are_free t =
    VM.appi (fn (v, i) =>
             if real_count v t = i
             then ()
             else raise Conformance "free variable set incorrect") 
    (freevars t)

  fun map_eq (m1, m2) = EQUAL = VM.collate Int.compare (m1, m2)

  local
    fun sum l = foldr (VM.unionWith op+) VM.empty l
    fun remove v m = #1 (VM.remove (m, v)) handle _ => m
  in
    fun real_map t =
      case look t of
        $ _ => VM.empty
      | V v => VM.insert(VM.empty, v, 1)
      | l / r => sum [real_map l, real_map r]
      | x \ a => remove x (real_map a)
      | S al => sum (map real_map al)
      | B (vl, a) => foldr (fn (v, m) => remove v m) (real_map a) vl
  end

  fun correct_map t =
    if map_eq (real_map t, freevars t)
    then ()
    else raise Conformance "maps are wrong"

  fun self_equal t = 
    if ast_cmp (t, t) = EQUAL
    then ()
    else raise Conformance "not equal to self"

  fun rebuild (t : ast) =
    case look t of
      $ l => $$ l
    | V v => VV v
    | x \ y => x \\ rebuild y
    | x / y => rebuild x // rebuild y
    | S xl => SS (map rebuild xl)
    | B (xl, t) => BB (xl, rebuild t)

  fun shallowbuild (t : ast) =
    case look t of
      $ l => $$ l
    | V v => VV v
    | x \ y => x \\ y
    | x / y => shallowbuild x // shallowbuild y
    | S xl => SS (map shallowbuild xl)
    | B (xl, t) => BB (xl, t)

  fun rebuild_eq t =
    if ast_cmp (t, rebuild t) = EQUAL andalso
       ast_cmp (rebuild t, t) = EQUAL andalso
       ast_cmp (rebuild t, rebuild t) = EQUAL andalso
       ast_cmp (t, shallowbuild t) = EQUAL andalso
       ast_cmp (rebuild t, shallowbuild t) = EQUAL
    then ()
    else raise Conformance ("not equal to rebuild: " ^ ttos t)

  val () =
    let

      (* known regressions first. *)

      val new_bug = sub (VV "x" // VV "y") "y" ("q" \\ VV "y")
      val () = correct_map new_bug

      (* bind variable and don't use it... *)
      val subst_bug = "x" \\ VV "y"
      (* open it. now we have a substitution *)
      val subst_bug = case look subst_bug of
                        _ \ t => t
                      | _ => raise Conformance "lam wasn't lam"
      (* and so the bound variable looks free since it
         is in the codomain of the substitution. *)
      val () = correct_map subst_bug

      val vars = ["w", "x", "y", "z"]
      val terms_base =
        [VV "x",
         VV "y",
         VV "z",
         $$ "leaf",
         VV "x" // VV "y",
         "x" \\ VV "x",
         "x" \\ VV "y",
         "x" \\ (VV "x" // VV "x"),
         "x" \\ (SS [VV "x", VV "x", VV "y"]),
         "x" \\ "x" \\ VV "x",
         "x" \\ "y" \\ VV "x",
         "x" \\ "y" \\ VV "y",
         "x" \\ (VV "x" // "x" \\ VV "x"),
         BB (["x"], VV "x"),
         BB (["x", "y"], VV "x"),
         BB (["y", "x"], VV "x"),
         BB (["x"], VV "y"),
         BB (["x"], VV "x" // VV "y"),
         BB ([], VV "x"),
         BB ([], $$ "leaf"),
         VV "x" // ("x" \\ VV "x"),
         subst_bug,
         new_bug
         ]
        
      val () = app self_equal terms_base
      val () = app (correct_count vars) terms_base
      val () = app free_are_free terms_base
      val () = app rebuild_eq terms_base
      val () = app correct_map terms_base
        
      (* [t/x]t'  for every term, var, term above *)
      val terms_subst =
        List.concat
        (
         map (fn t' =>
              List.concat
              (map (fn t =>
                    (map (fn v => 
                          let 
                            val r = sub t' v t
                          in
                            (* print (ttos t' ^ " for " ^ v ^ " in " ^ ttos t ^ " is:\n    " ^ ttos r ^"\n"); *)
                            r
                          end) vars)) terms_base)) terms_base
         )
        
      val () = app self_equal terms_subst
      val () = print "equal ok.\n"
      val () = app (correct_count vars) terms_subst
      val () = print "count ok.\n"
      val () = app free_are_free terms_subst
      val () = print "free ok.\n"
      val () = app rebuild_eq terms_subst
      val () = print "rebuild ok.\n"
      val () = app correct_map terms_subst
      val () = app correct_map (map rebuild terms_subst)
      val () = app correct_map (map shallowbuild terms_subst)

      (* some example substitutions and results *)
      val substs =
        [(VV "x", "z", VV "y", VV "y"),
         (VV "x", "y", VV "y", VV "x"),
         (VV "x", "x", VV "x", VV "x"),
         ("x" \\ VV "x", "y", VV "z", VV "z"),
         (* test alpha equivalence here *)
         ("x" \\ VV "x", "z", VV "z", "z" \\ VV "z"),
         ("x" \\ VV "y", "z", VV "z", "z" \\ VV "y"),
         ("x" \\ VV "y", "x", VV "x", "z" \\ VV "y"),
         ("x" \\ VV "y", "y", VV "y", "z" \\ VV "y"),
         ("x" \\ VV "y", "z", "y" \\ VV "z", "u" \\ "v" \\ VV "y"),
         ("x" \\ VV "x", "z", BB (["z", "w"], VV "z"), BB (["z", "w"], VV "z")),
         ("x" \\ VV "x", "z", BB (["w", "z"], VV "z"), BB (["w", "z"], VV "z")),
         ("x" \\ VV "x", "z", BB (["y", "w"], VV "z"), BB (["z", "w"], "x" \\ VV "x")),
         ("x" \\ VV "z", "z", BB (["y", "w"], VV "z"), BB (["w", "y"], "x" \\ VV "z")),
         (BB (["x", "y"], VV "z"), "w", BB (["x", "y"], VV "w"), BB(["x", "y"],
                                                                    BB(["q", "w"],
                                                                       VV "z"))),
         (BB (["x", "y"], VV "x"), "w", BB (["x", "y"], VV "w"), BB(["q", "y"],
                                                                    BB(["x", "w"],
                                                                       VV "x"))),
         (BB (["y", "x"], VV "x"), "w", BB (["x", "y"], VV "w"), BB(["q", "y"],
                                                                    BB(["w", "x"],
                                                                       VV "x"))),
         (BB (["x", "y", "z"],
              "w" \\ VV "x"), "z", "w" \\ "x" \\ (VV "z" // 
                                                  BB(["q", "a"], VV "z" // VV "a")),
          "w" \\ "xx" \\ BB (["x", "y", "z"],
                             "w" \\ VV "x") //
                         BB (["qq", "a"], BB (["x", "y", "z"],
                                              "w" \\ VV "x") // VV "a")),

         (SS [VV "x", VV "y", VV "z",
              "w" \\ VV "x"], "z", "w" \\ "x" \\ (VV "z" // 
                                                  BB(["q", "a"], VV "z" // VV "a")),
          "w" \\ "xx" \\ (SS [VV "x", VV "y", VV "z",
                              "w" \\ VV "x"] //
                          BB (["qq", "a"], SS [VV "x", VV "y", VV "z",
                                               "w" \\ VV "x"] // VV "a")))
         ]

      fun subst_correct (small, x, big, res) =
          let val r = sub small x big
          in
            (if ast_cmp (r, res) = EQUAL
             then ()
             else raise Conformance "substitution result incorrect");
            self_equal r;
            correct_count vars r;
            correct_map r;
            free_are_free r;
            rebuild_eq r
          end

      val () = app subst_correct substs
      val () = app subst_correct (map (fn (a, b, c, d) => (rebuild a, b, c, d)) substs)
      val () = app subst_correct (map (fn (a, b, c, d) => (a, b, c, rebuild d)) substs)
      val () = app subst_correct (map (fn (a, b, c, d) => (a, b, rebuild c, d)) substs)
      val () = app subst_correct (map (fn (a, b, c, d) => (shallowbuild a, b, rebuild c, d)) substs)
      val () = app subst_correct (map (fn (a, b, c, d) => (a, b, shallowbuild c, rebuild d)) substs)
      val () = print "substs ok.\n"
    in
      ()
    end handle (e as Conformance s) =>
      let in
        print ("AST Conformance failed: " ^ s ^ "\n");
        raise e
      end


end
