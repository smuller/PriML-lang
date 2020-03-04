
(* Integer constants throughout the compiler. This makes it
   easier to switch from 32-bit integers to 64, or infinite
   precision.

   XXX should be abstract!

   *)

(* XXX convert this to intinf? What does javascript support? *)
structure IntConst =
struct
  type intconst = Word32.word

  (* don't want to print as a hex constant... *)
  (* val tostring = Word32.toString *)
  val tostring = IntInf.toString o Word32.toLargeInt

  fun fromstring s =
    case IntInf.fromString s of
      NONE => NONE
        (* XXX overflow ... *)
    | SOME i => SOME(Word32.fromLargeInt i)

  val fromInt = Word32.fromInt
    
  val toString = tostring
  val fromString = fromstring
  val toInt = Word32.toIntX

  val compare = Word32.compare

  fun toReal x = Real.fromLargeInt (Word32.toLargeIntX x)
end
