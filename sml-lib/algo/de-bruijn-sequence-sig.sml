
signature DE_BRUIJN_SEQUENCE =
sig

  (* debruijn (l, r)
     Returns a de bruijn sequence for an alphabet with radix r,
     where every possible sequence of length l appears once as
     a substring. 

     Note: The algorithm is from the internet and I don't
     understand it, so it might not be correct. It works as
     expected for small test cases. *)
  val debruijn : int * int -> int list

end
