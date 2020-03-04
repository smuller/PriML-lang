(* Based on
   Joe Sawada and Frank Ruskey, "An Efficient Algorithm for Generating Necklaces with Fixed Density", SIAM Journal of Computing 29:671-684, 1999.

   through the grapevine. *)

structure DeBruijnSequence :> DE_BRUIJN_SEQUENCE =
struct

  fun debruijn (len, radix) =
    let
      val a = Array.array (len * radix + 1, 0)

      val revout = ref nil
      fun db (t, p) =
        if t > len
        then
           if len mod p = 0
           then
             Util.for 1 p (* (p + 1) *)
             (fn j =>
              revout := Array.sub(a, j) :: !revout)
           else ()
        else
          let in
            Array.update(a, t, Array.sub(a, t - p));
            db (t + 1, p);
            Util.for (Array.sub(a, t - p) + 1) (radix - 1)
            (fn j =>
             let in
               Array.update(a, t, j);
               db (t + 1, t)
             end)
          end

      val () = db (1, 1)
      val r = rev (!revout)
    in

      (* The above generates a sequence that, if circular,
         contains all substrings exactly once. But we want a single
         sequence. Append enough beginning chars to achieve that. *)
      r @ List.take (r, len - 1)
    end

end
