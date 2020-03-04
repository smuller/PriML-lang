
signature ILPRINT =
sig

    (* attempts to use type abbreviations to print
       datatypes if in scope (see muhelp). *)
    val ttolex : (string -> string option) -> IL.typ -> Layout.layout

    (* type, world, expression, declaration, and unit  to layout. *)
    val ttol : IL.typ    -> Layout.layout
    val wtol : IL.world  -> Layout.layout
    val etol : IL.exp    -> Layout.layout
    val dtol : IL.dec    -> Layout.layout
    val utol : IL.ilunit -> Layout.layout
    val vtol : IL.value  -> Layout.layout
    val ptol : ('a -> Layout.layout) -> 'a IL.poly -> Layout.layout

end
