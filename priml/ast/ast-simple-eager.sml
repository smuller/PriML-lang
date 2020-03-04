(* This simple version of the AST caches counts of free
   variables in order to speed up substitution and
   free variable checks. *)

(* TODO: 
         use vectors instead of lists?
         hash cons?
         hash for quick equality tests 
         delayed substitutions

*)

(* Tried:

   de Bruijn - speeds up compares, but is quite complicated.
               debruijnizing costs at bind time, and then again
               at unbind time.
               biggest problem: free var counts are impossible
               to maintain with explicit (var/db) substitutions
               unless we also have free db sets, which are
               more difficult to maintain. (When computing the
               free vars of an explicit substitution, we only
               count the vars in the codomain when the correpsonding
               index in the domain is free.)

*)

functor ASTFn(A : ASTARG) :> AST where type var  = A.var
                                   and type leaf = A.leaf =
struct
  open A

  fun I x = x
  infixr 9 `
  fun a ` b = a b

  structure VM = SplayMapFn(type ord_key = var
                            val compare = var_cmp)

  structure Susp :>
  sig
    type 'a susp
    val memoize : (unit -> 'a) -> 'a susp
    val imm : 'a -> 'a susp
    val force : 'a susp -> 'a
  end =
  struct
    type 'a susp = unit -> 'a

    (* memoize a unit -> 'a function so that it is only
       run the first time it is called. *)
    fun memoize f =
      let
        val r = ref NONE
      in
        (fn () =>
         case !r of
           NONE =>
             let val x = f ()
             in
               r := SOME x;
               x
             end
         | SOME x => x)
      end

    fun imm x () = x
    fun force f = f ()
  end

  structure Eager :>
  sig
    type 'a susp
    val memoize : (unit -> 'a) -> 'a susp
    val imm : 'a -> 'a susp
    val force : 'a susp -> 'a
  end =
  struct
    type 'a susp = 'a
    fun memoize f = f ()
    fun imm x = x
    fun force f = f
  end

  (* or susp... *)
  open Eager

  datatype 'ast front =
    $ of leaf
    (* bind, bind list *)
  | \ of var * 'ast
  | B of var list * 'ast
    (* sequence, sequence list *)
  | / of 'ast * 'ast
  | S of 'ast list
  | V of var

  infixr / \

  (* exception AST of string *)
  val AST = Exn

  (* First attempt. Just counting free vars. 
     invariant: the integer is strictly positive
     *)
  datatype ast =
    A of { m : int VM.map susp,
           f : ast front }

  val empty = imm (VM.empty : int VM.map)

  fun sum l = foldr (VM.unionWith op+) VM.empty l
  fun mult n m = VM.map (fn occ => occ * n) m

  fun getmap (A { m, ... }) = m
  (* remove, even if it is not present *)
  fun remove v m = #1 (VM.remove (m, v)) handle _ => m

  fun hide ($ l) = A { m = empty,
                       f = $ l }
    | hide (V v) = A { m = imm (VM.insert(VM.empty, v, 1)),
                       f = V v }
    | hide (S al) = A { m = memoize (fn () =>
                                     let val ms = map (force o getmap) al
                                     in sum ms
                                     end),
                        f = S al }
    | hide (a1 / a2) = A { m = memoize (fn () => sum [force ` getmap a1, force ` getmap a2]),
                           f = a1 / a2 }
    | hide (v \ a) = A { m = memoize (fn () => remove v (force ` getmap a)),
                         f = v \ a }
    | hide (B (vl, a)) = A { m = memoize (fn () => foldr (fn (v, m) => remove v m) (force ` getmap a) vl),
                             f = B (vl, a) }


  fun freevars (A { m, ... }) = force m

  fun isfree ast v =
    case VM.find(freevars ast, v) of
      NONE => false
    | SOME x => true

  fun count ast v =
    (case VM.find(freevars ast, v) of
       NONE => 0
     | SOME n => n)

  (* PERF should delay substitutions and renamings. *)
  fun rename nil ast = ast
    | rename ((v,v') :: t) ast =
    let 
      (* val () = print ("Rename " ^ var_tostring v ^ " -> " ^ var_tostring v' ^ "\n"); *)
      val ast = rename t ast
      val ast = sub (hide ` V v') v ast
    in ast
    end

  and sub (obj as A { m = mobj, ... }) v (ast as A { m, f }) =
    (* get out early *)
    if isfree ast v
    then 
      let 
        (* we know the variable occurs, so the map will include all of obj's
           free vars (occurring as many times as the variable occurs) *)
        val x = count ast v
        val m = remove v (freevars ast)
        val multobj = mult x (force mobj)
        val m = imm (sum [multobj, m])
      in
        case f of
          $l => raise Exn "impossible: leaf has free var"
        | V v' => if var_eq (v, v')
                  then obj
                  else raise Exn "impossible: var has other var as free var"
        | a1 / a2 => A { m = m,
                         f = sub obj v a1 / sub obj v a2 }
        | v' \ a => (* avoid renaming if v' doesn't appear in obj... *)
                    if isfree obj v'
                    then 
                      let 
                        val v'' = var_vary v'
                        val a = rename [(v', v'')] a
                      in
                        print "avoid \\\n";
                        A { m = m,
                            f = v'' \ sub obj v a }
                      end
                    else
                      A { m = m,
                          f = v' \ sub obj v a }

        | S al => A { m = m,
                      f = S ` map (sub obj v) al }
        | B (vl, a) =>
                  (* PERF could only rename the actually occuring vars. *)
                  if List.exists (isfree obj) vl
                  then
                    let
                      val subst = ListUtil.mapto var_vary vl
                      val a = rename subst a
                    in
                      print "avoid B\n";
                      A { m = m,
                          f = B (map #2 subst, sub obj v a) }
                    end
                  else A { m = m,
                           f = B (vl, sub obj v a) }
      end
    else ast

  fun looky self (A { m = _, f }) = 
    (case f of
       $l => $l
     | V v => V v
     | a1 / a2 => self a1 / self a2
     | S al => S (map self al)
     | v \ a =>
       let val v' = var_vary v
           val a = rename [(v, v')] a
       in v' \ self a
       end
     | B (vl, a) =>
       let val subst = ListUtil.mapto var_vary vl
           val a = rename subst a
       in
         B (map #2 subst, self a)
       end)

  fun ast_cmp (A{ f = $l1, ... }, A{ f = $l2, ... }) = leaf_cmp (l1, l2)
    | ast_cmp (A{ f = $_, ... }, _) = LESS
    | ast_cmp (_, A{ f = $_, ... }) = GREATER
    | ast_cmp (A{ f = V v1, ... }, A{ f = V v2, ... }) = var_cmp (v1, v2)
    | ast_cmp (A{ f = V _, ... }, _) = LESS
    | ast_cmp (_, A{f = V _, ... }) = GREATER
    | ast_cmp (A{ f = a1 / b1, ... }, A{ f = a2 / b2, ... }) =
    (case ast_cmp (a1, a2) of
       LESS => LESS
     | GREATER => GREATER
     | EQUAL => ast_cmp (b1, b2))
    | ast_cmp (A{ f = _ / _, ... }, _) = LESS
    | ast_cmp (_, A{ f = _ / _, ...}) = GREATER
    | ast_cmp (A{ f = S l1, ...}, A{ f = S l2, ... }) = astl_cmp (l1, l2)
    | ast_cmp (A{ f = S _, ...}, _) = LESS
    | ast_cmp (_, A{ f = S _, ...}) = GREATER
    | ast_cmp (A{ f = v1 \ a1, ...}, A { f = v2 \ a2, ... }) =
       let 
         val v' = var_vary v1
           (*
         val () = print ("cmp " ^ var_tostring v1 ^ "," ^ var_tostring v2 ^ " -> " ^
                         var_tostring v' ^ "\n")
            *)
         val a1 = rename [(v1, v')] a1
         val a2 = rename [(v2, v')] a2
       in
         ast_cmp (a1, a2)
       end
    | ast_cmp (A { f = _ \ _, ...}, _) = LESS
    | ast_cmp (_, A { f = _ \ _, ...}) = GREATER
    | ast_cmp (A { f = B(vl1, a1), ...}, A{ f = B(vl2, a2), ... }) =
       let
         val vl' = map var_vary vl1
         val s1 = ListPair.zip (vl1, vl')
         val s2 = ListPair.zip (vl2, vl')
           (*
         val () = print "B:\n"
         val () = ListUtil.app3 (fn (v1, v2, v') =>
                                 print ("  cmpB " ^ var_tostring v1 ^ "," ^ var_tostring v2 ^ " -> " ^
                                        var_tostring v' ^ "\n")
                                 ) vl1 vl2 vl'
         val () = print "end\n"
            *)
         val a1 = rename s1 a1
         val a2 = rename s2 a2
       in
         ast_cmp (a1, a2)
       end

  and astl_cmp (nil, nil) = EQUAL
    | astl_cmp (nil, _ :: _) = LESS
    | astl_cmp (_ :: _, nil) = GREATER
    | astl_cmp (h1 :: t1, h2 :: t2) =
       (case ast_cmp (h1, h2) of
          LESS => LESS
        | GREATER => GREATER
        | EQUAL => astl_cmp (t1, t2))
       

  fun look ast = looky I ast
  fun look2 ast = looky look ast
  fun look3 ast = looky look2 ast
  fun look4 ast = looky look3 ast
  fun look5 ast = looky look4 ast


  val $$ = hide o $
  val \\ = hide o op \
  val // = hide o op /
  val SS = hide o S
  val BB = hide o B
  val VV = hide o V

end
