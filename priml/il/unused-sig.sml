signature ILUNUSED =
sig

  exception Unused of string
  
  val unused : IL.ilunit -> IL.ilunit

end