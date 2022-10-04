
(* Extract the name of the datatype that created a mu, if possible.
   Just used for error messages. *)
structure MuName =
struct

  fun name ctx thisc =
    (case Context.con ctx thisc of
       (kind, IL.Lambda f, _) =>
         (case kind of
            0 => SOME thisc
          (* XXX otherwise do anti-unification
             or whatever to figure out what
             the datatype "type constructor"
             is applied to. (but we should be
             careful that unification doesn't
             cause any harmful side-effects.) *)
          | _ => NONE)

     (* doesn't look like a datatype! *)
     | _ => NONE)
       (* totally normal for this to be out of
          scope right now *)
       handle Context.Absent _ => NONE

end
