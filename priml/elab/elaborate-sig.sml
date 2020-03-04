
signature ELABORATE =
sig

    exception Elaborate of string

    val elaborate : EL.prog -> IL.prog

end
