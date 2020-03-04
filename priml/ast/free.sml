
(* Fills in some functions "for free," if the AST implementation doesn't
   permit an efficient implementation. *)
functor FreeAST(structure A : ASTARG
                structure B : AST_BASE where type var = A.var
                                         and type leaf = A.leaf
                ) :> AST where type var  = A.var
                           and type leaf = A.leaf 
                           and type ast  = B.ast =
struct

  open A
  open B

  structure VM = SplayMapFn(type ord_key = var
                            val compare = var_cmp)

  infixr \ / \\ // 

  fun count (a : ast) (x : var) =
    case look a of
      V y => if var_eq(x, y) then 1 else 0
    | l / r => count l x + count r x
    | _ \ r => count r x
    | S l => foldr op+ 0 (map (fn a => count a x) l)
    | B (_, r) => count r x
    | $ _ => 0

  fun isfree x a = count x a > 0

  fun sum l = foldr (VM.unionWith op+) VM.empty l
  fun remove v m = #1 (VM.remove (m, v)) handle _ => m


  fun freevars a =
    case look a of
       $l => VM.empty
     | V v => VM.insert(VM.empty, v, 1)
     | S al => sum (map freevars al)
     | a1 / a2 => sum [freevars a1, freevars a2]
     | v \ a => remove v (freevars a)
     | B (vl, a) => foldr (fn (v, m) => remove v m) (freevars a) vl

  fun rename nil ast = ast
    | rename ((v,v') :: t) ast =
    let 
      val ast = rename t ast
      val ast = sub (hide (V v')) v ast
    in ast
    end

  and sub (obj : ast) (v : var) (ast : ast) =
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
                    let
                      val subst = ListUtil.mapto var_vary vl
                      val a = rename subst a
                    in
                      BB (map #2 subst, sub obj v a)
                    end
      end

  fun ast_cmp' ($l1, $l2) = leaf_cmp (l1, l2)
    | ast_cmp' ($_, _) = LESS
    | ast_cmp' (_, $_) = GREATER
    | ast_cmp' (V v1, V v2) = var_cmp (v1, v2)
    | ast_cmp' (V _, _) = LESS
    | ast_cmp' (_, V _) = GREATER
    | ast_cmp' (a1 / b1, a2 / b2) =
    (case ast_cmp (a1, a2) of
       LESS => LESS
     | GREATER => GREATER
     | EQUAL => ast_cmp (b1, b2))
    | ast_cmp' (_ / _, _) = LESS
    | ast_cmp' (_, _ / _) = GREATER
    | ast_cmp' (S l1, S l2) = astl_cmp (l1, l2)
    | ast_cmp' (S _, _) = LESS
    | ast_cmp' (_, S _) = GREATER
    | ast_cmp' (v1 \ a1, v2 \ a2) =
       let 
         val v' = var_vary v1
         val a1 = rename [(v1, v')] a1
         val a2 = rename [(v2, v')] a2
       in
         ast_cmp (a1, a2)
       end
    | ast_cmp' (_ \ _, _) = LESS
    | ast_cmp' (_, _ \ _) = GREATER
    | ast_cmp' (B(vl1, a1), B(vl2, a2)) =
       let
         val vl' = map var_vary vl1
         val s1 = ListPair.zip (vl1, vl')
         val s2 = ListPair.zip (vl2, vl')
         val a1 = rename s1 a1
         val a2 = rename s2 a2
       in
         ast_cmp (a1, a2)
       end

  and ast_cmp (a1, a2) = ast_cmp' (look a1, look a2)

  and astl_cmp (nil, nil) = EQUAL
    | astl_cmp (nil, _ :: _) = LESS
    | astl_cmp (_ :: _, nil) = GREATER
    | astl_cmp (h1 :: t1, h2 :: t2) =
       (case ast_cmp (h1, h2) of
          LESS => LESS
        | GREATER => GREATER
        | EQUAL => astl_cmp (t1, t2))

  fun layout _ = Layout.str "unimplemented"

end
