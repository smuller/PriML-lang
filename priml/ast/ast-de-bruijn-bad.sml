(* This version of the AST uses de Bruijn indices
   to represent bound variables. Free variables are
   still represented by name. 

   We bias the representation to make 'looking' at
   a term more efficient than creating a term. *)

(* TODO: de Bruijn
         use vectors instead of lists?
         hash cons?
         hash for quick equality tests 
         delayed substitutions

         compliance suite for this; it is surprisingly easy
         to make mistakes (esp. with delayed free variable
         sets, etc.). *)

functor ASTFn(A : ASTARG) : AST where type var  = A.var
                                  and type leaf = A.leaf =
struct
  open A

  fun I x = x
  fun K x y = x
  infixr 9 `
  fun a ` b = a b

  datatype 'ast front =
    $ of leaf
    (* bind, bind list *)
  | \ of var * 'ast
  | B of var list * 'ast
    (* sequence, sequence list *)
  | / of 'ast * 'ast
  | S of 'ast list
  | V of var

  infixr / \ // \\

  structure VM = SplayMapFn(type ord_key = var
                            val compare = var_cmp)

  (* exception AST of string *)
  val AST = Exn

  val ltov = Vector.fromList
  fun vtol v = Vector.foldr op:: nil v

  datatype term =
      Leaf of leaf
      (* if bool is true, then the vector contains
         a single element.
         the variables in the vector are only for
         the purpose of creating new named variables
         with the same base name as the original lams;
         it is the length of the vector that determines
         the number of nameless de Bruinj bindings. *)
    | Lam of bool * var vector * ast
      (* if boolean is true, then the vector contains
         exactly two terms. *)
    | Agg of bool * ast vector
    | Var of var
    | Subst of subst * ast
      (* 0-based, non-negative *)
    | Index of int

  (* PERF could also perhaps keep an interval of de Bruijn indices that appear? *)
  and ast = A of { f : term, m : int VM.map }

  (* A substitution consists of two operations to be carried out on a de
     Bruin index.

     If the index is less than 'skip', it is unaffectd. When we push a
     substitution into a binder, we increment its skip, since it
     cannot have any effect on that bound variable. (If it is not less
     than skip, we subtract skip from it before indexing into the
     vector. Otherwise, the first skip elements of the replacement
     vector are always wasted.)

     This subtracted index is either in the domain of the
     substitution, or too high (larger than or equal to the length of
     the vector). If it is too high we return the index plus 'up'. (Up
     is always at least as large as the length of the vector.) When a
     substitution is pushed under a binder, we apply to its codomain a
     new substitution 'up' because any de Bruin indices in there now
     look past the binder we've just pushed it under.

     Otherwise, we simply select the element from the substitution
     vector. The vector [t0, t1, t2 ... tn] is taken to mean t0/0,
     t1/1, t2/2 ... tn/n and the identity for any other index. *)

  withtype subst = { r    : ast vector,
                     up   : int,
                     skip : int }

  fun count (A { m, ...}) v =
    (case VM.find(m, v) of
       NONE => 0
     | SOME n => n)

  fun isfree a x = count a x > 0

  fun sumv l = Vector.foldr (fn (A { m, ...}, b) => VM.unionWith op+ (m, b)) VM.empty l

  fun Var' v = A { f = Var v, m = VM.insert(VM.empty, v, 1) }
  fun Leaf' l = A { f = Leaf l, m = VM.empty }
  fun Agg' (b, v : ast vector) = A { f = Agg (b, v), m = sumv v }
  (* doesn't contribute to free vars, since these are all bound *)
  fun Lam' (b, vl, a as A { m, ... }) = A { f = Lam (b, vl, a), m = m }
  fun Index' i = A { f = Index i, m = VM.empty }
  (* FIXME to get an accurate count of free variables, we need to know
     whether the de Bruinj indices being substituted for actually occur or not.
     If they do not, then we will overcount in the case that the codomain of
     the substitution has free variables in it. *)
  fun Subst' (s as { r, ... }, t as A { m, ... }) = A { f = Subst (s, t),
                                                        m = VM.unionWith op+ (m, sumv r) }

  (* find named variables in 'vars'. replace them with de bruinj
     indices, assuming we are at given depth. The variables should
     appear in such that the first variable in the list is the
     innermost bound. We do this eagerly, since our delayed
     substitutions can only substitute for de Bruinj variables. *)
  fun bind' depth vars term =
    (case term of
       Leaf l => Leaf' l
     | Index i => Index' i
     | Agg (b, v) => Agg' (b, Vector.map (bind depth vars) v)
     | Lam (b, vs, a) => Lam' (b, vs, bind (depth + Vector.length vs) vars a)
(* simpler to just push the substitution,
   especially since we are doing a linear traversal. 
     | Subst ({ r, up, skip }, t) => 
         Subst ({ (* still at the same scope -- right? *)
                  r = Vector.map (bind depth vars) tv,
                  up = up,
                  skip = skip },
                bind depth vars t)
*)
     | Subst (s, t) => bind depth vars (push s t)
     | Var v =>
         let
           fun rep _ nil = Var' v
             | rep n (vv :: rest) = if var_eq (v, vv)
                                    then Index' n
                                    else rep (n + 1) rest
         in
           rep depth vars
         end)

  (* PERF get out early if no var occurs in f, using freevar set *)
  and bind depth vars (a as A { f, ... }) =
    if List.exists (isfree a) vars
    then bind' depth vars f
    else a

  (* apply the substitution s to t one level. *)
  and push' (s as { r, up, skip }) (term : term) =
    (case term of
       Subst (ss, tt) => 
         let in
           (* PERF the whole point of doing it this
              way is that we can compose substitutions!
              this way makes linear chains of pushes... *)
           (* print "subst hit subst\n"; *)
           push s (push ss tt)
         end
     | Index i => if i < skip
                  then Index' i
                  else let val i = i - skip
                       in
                         if i >= Vector.length r
                         then Index' (i + up)
                         else Vector.sub(r, i)
                       end
     | Var v => Var' v
     | Leaf l => Leaf' l
     | Agg (b, v) => Agg' (b, Vector.map (fn tm => Subst'(s, tm)) v)
     (* shifts the substitution up in the body of the lambda, as
        well as within the substituted terms. *)
     | Lam (b, vs, t) => 
         let
         in
           (* HERE we should collect only the vars that are actually bound.
              We need this later to compute accurate freevar sets, because

              ... actually that does not work, since being free in one branch
              of an AGG doesn't mean that it's free in all branches (obviously)
              so once we push a subst past an agg, it becomes inaccurate again.
              *)
           Lam' (b, vs, 
                 Subst'( { (* increment the codomain *)
                           r = Vector.map (fn tm =>
                                           Subst' ({ r = Vector.fromList nil,
                                                     up = Vector.length vs,
                                                     skip = 0 },
                                                   tm)) r,
                           (* maintain the same initial shift ? *)
                           up = up,
                           (* ignore the lowest bindings *)
                           skip = skip + Vector.length vs }, t)))
         end

  and push s (A { f, ... }) = push' s f

  fun hide (V v) = Var' v
    | hide ($ l) = Leaf' l
    | hide (a1 / a2) = Agg' (true, ltov [a1, a2])
    | hide (S al) = Agg' (false, ltov al)
    | hide (v \ a) = Lam' (true, ltov [v], bind 0 [v] a)
    | hide (B (vl, a)) = Lam' (false, ltov vl, bind 0 (rev vl) a)

  fun vrev v = Vector.fromList (rev (vtol v)) (* PERF *)

  fun looky' self term =
    (case term of
       Leaf l => $l
     | Var v => V v
     | Index _ => raise Exn "bug: looked at index!"
     | Lam (b, vs, t) =>
         let 
           val vs = Vector.map var_vary vs
           val vsub = vrev (Vector.map Var' vs)
         in
           if b
           then (Vector.sub (vs, 0) \ self ` Subst' ( { r = vsub, up = 0, skip = 0 }, t ))
           else B (vtol vs, self ` Subst'( { r = vsub, up = 0, skip = 0 }, t))
         end
     | Agg (true, v)  =>
         let val a = Vector.sub(v, 0)
             val b = Vector.sub(v, 1)
         in
           self a / self b
         end
     | Agg (false, v) => S (map self (vtol v))
     | Subst (s, t) => looky self (push s t))

  and looky self (A { f, ... }) = looky' self f

  fun ast_cmp' (Leaf l1, Leaf l2) = leaf_cmp (l1, l2)
    | ast_cmp' (Leaf _, _) = LESS
    | ast_cmp' (_, Leaf _) = GREATER
    | ast_cmp' (Var v1, Var v2) = var_cmp (v1, v2)
    | ast_cmp' (Var _, _) = LESS
    | ast_cmp' (_, Var _) = GREATER
    | ast_cmp' (Agg (b1, l1), Agg (b2, l2)) = 
    (case Util.bool_compare (b1, b2) of 
       (* PERF make astv_cmp *)
       EQUAL => astl_cmp (vtol l1, vtol l2)
     | order => order)
    | ast_cmp' (Agg _, _) = LESS
    | ast_cmp' (_, Agg _) = GREATER
    | ast_cmp' (Index i, Index j) = Int.compare (i, j)
    | ast_cmp' (Index _, _) = LESS
    | ast_cmp' (_, Index _) = GREATER
    (* ignore the advisory variable names *)
    | ast_cmp' (Lam(b1, _, a1), Lam(b2, _, a2)) =
       (case Util.bool_compare (b1, b2) of
          EQUAL => ast_cmp (a1, a2)
        | order => order)
    | ast_cmp' (Subst _, _) = raise Exn "impossible!"
    | ast_cmp' (_, Subst _) = raise Exn "impossible!"

  and ast_cmp (A { f = Subst (s, t), ... }, a) = ast_cmp (push s t, a)
    | ast_cmp (a, A { f = Subst (s, t), ... }) = ast_cmp (a, push s t)
    | ast_cmp (A { f = a, ...}, 
               A { f = b, ...}) = ast_cmp' (a, b)

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
  val op \\ = hide o op \
  val op // = hide o op /
  val SS = hide o S
  val BB = hide o B
  val VV = hide o V

  fun sum l = foldr (VM.unionWith op+) VM.empty l
  fun remove v m = #1 (VM.remove (m, v)) handle _ => m

  fun freevars (A { m, ... }) = m

  (* PERF stub implementations force conversion between
     representations *)
  fun rename nil ast = ast
    | rename ((v,v') :: t) ast =
    let 
      val ast = rename t ast
      val ast = sub (hide (V v')) v ast
    in ast
    end

  and sub (obj : ast) (v : var) (ast : ast) =
    if isfree ast v
    then
      let 
      in
        case look ast of
          $l => ast
        | V v' => if var_eq (v, v')
                  then obj
                  else ast
        | a1 / a2 => sub obj v a1 // sub obj v a2
        | v' \ a => let 
                      val v'' = var_vary v'
                      val a = rename [(v', v'')] a
                    in
                      v'' \\ sub obj v a
                    end

        | S al => SS (map (sub obj v) al)

        | B (vl, a) =>
                  if List.exists (isfree obj) vl
                  then
                    let
                      val subst = ListUtil.mapto var_vary vl
                      val a = rename subst a
                    in
                      BB (map #2 subst, sub obj v a)
                    end
                  else BB (vl, sub obj v a)
      end
    else ast

end

(*
functor ASTFn(A : ASTARG) : (* XXX :> *) AST where type var  = A.var
                                               and type leaf = A.leaf =
struct
  structure B = AST1(A)
  structure C = FreeAST(structure A = A
                        structure B = B)

  open C
  open B
end
*)