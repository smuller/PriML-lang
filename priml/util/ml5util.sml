structure ML5pghUtil =
struct
    infixr 9 `
    fun a ` b = a b

    val itos = Int.toString

    local val ctr = ref 0
    in
        fun newstring sep s =
            let in
                ctr := (!ctr + 1);
                s ^ sep ^ itos ` !ctr
            end

        val newstr = newstring "_"
    end

    (* any legal comparison that puts ints (encoded in ascii)
       in the correct order *)
    fun labelcompare (l1, l2) =
        (case (Int.fromString l1, Int.fromString l2) of
             (NONE, NONE) => String.compare (l1, l2)
           | (SOME _, NONE) => LESS
           | (NONE, SOME _) => GREATER
           | (SOME x, SOME y) =>
                 (case Int.compare (x, y) of
                      LESS => LESS
                    | GREATER => GREATER
                    | EQUAL => String.compare (l1, l2)))

    fun pathcompare (a, b) =
        Util.lex_order (Util.option_compare String.compare)
                       String.compare (a, b)

    local
        (* DES gives a pretty good source of randomness *)
        val r = ref (0wxBEEFDEAD : Word32.word)
        val k = DES.key (0wxABCD1234, 0wxe707f312)
    in
        fun randomword () =
            let
            in
                r := !r * 0wx31337;
                r := (Word32.xorb (!r, 0wxFEED9876));
                r := #1 (DES.encrypt k (0wx00001111, !r));
                !r
            end
    end
end

structure StringMap = SplayMapFn(type ord_key = string val compare = String.compare)
structure StringMapUtil = MapUtil(structure M = StringMap)

structure StringSet = SplaySetFn(type ord_key = string val compare = String.compare)
structure StringSetUtil = SetUtil(structure S = StringSet)

structure IntMap = SplayMapFn(type ord_key = int val compare = Int.compare)
structure IntMapUtil = MapUtil(structure M = IntMap)

