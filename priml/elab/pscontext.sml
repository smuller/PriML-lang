
structure PSContext = 
struct
    open IL  

    exception PSConstraints of string

    (* NOTE: the key for PSEvarMap should only be PSEvar.
        There should be an error otherwise. *)
    fun compare (PSEvar _, PSSet _) = GREATER
      | compare (PSSet _, PSEvar _) = LESS
      | compare (PSSet s1, PSSet s2) = PrioSet.compare (s1, s2)
      | compare (PSEvar (ref (Bound _)), PSEvar (ref (Free _))) = GREATER
      | compare (PSEvar (ref (Free _)), PSEvar (ref (Bound _))) = LESS
      | compare (PSEvar (ref (Free n1)), PSEvar (ref (Free n2))) = Int.compare (n1, n2)
      | compare (PSEvar (ref (Bound w1)), PSEvar (ref (Bound w2))) = compare (w1, w2)

    structure PSEvarMap = SplayMapFn (struct
                                        type ord_key = prioset
                                        val compare = compare
                                      end)

    type pscontext = PrioSet.set PSEvarMap.map

end
