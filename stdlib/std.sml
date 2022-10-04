infix 5 +
infix 5 -
infix 8 *
infix 3 <=
infix 3 <
(* infix = special case *)
infix 3 >
infix 3 >=
infix 3 <>
      (*
(* PERF should inline *)
fun inline + (x, y) = primapp Plus { } (x, y)
fun inline - (x, y) = primapp Minus { } (x, y)
fun inline * (x, y) = primapp Times { } (x, y)
fun inline < (x, y) = primapp Less { } (x, y)
fun inline <=(x, y) = primapp Lesseq { } (x, y)
fun inline > (x, y) = primapp Greater { } (x, y)
fun inline >=(x, y) = primapp Greatereq { } (x, y)
(* this dec also special, in initial *)
(* fun inline = (x, y) = primapp Eq { } (x, y) *)
fun inline <>(x, y) = primapp Neq { } (x, y)

fun inline yield () = primapp Yield { } ( )
(* fun inline (t) halt () = primapp Halt { t } ( ) *)

infix 5 ^
fun inline ^(x, y) = [[x][y]]

infix 1 :=
(* fun inline (t) :=(r, a) = primapp Set { t } (r, a)
fun inline (t) ! r = primapp Get { t } (r)
fun inline (t) ref a = primapp Ref { t } (a) *)
fun inline :=(r, a) = primapp Set (r, a)
fun inline ! r = primapp Get (r)
fun inline ref a = primapp Ref (a)

infix 3 seq
fun inline seq (x, y) = primapp Eqs { } (x, y)
fun inline size s = primapp StringLength { } (s)
(* XXX bounds on these two? They can fail at runtime, but safely... *)
fun inline ssub (s, x) = primapp StringSub { } (s, x)
fun inline substring (s, start, len) = primapp StringSubstring { } (s, start, len)
fun inline string-replace (s, d, t) = primapp StringReplace { } (s, d, t)
fun inline ord c = primapp Ord { } (c)
(* XXX bounds checks for chr? We should probably just use 32-bit strings. *)
fun inline chr c = primapp Chr { } (c)
fun inline itos i = primapp IntToString { } (i)

(* fun inline array0 .. ? *)
(*fun inline (t) array (length, a : t) = primapp Array { t } (length, a)
fun inline (t) sub (arr, x) = primapp Sub { t } (arr, x)
fun inline (t) update (arr, x, a) = primapp Update { t } (arr, x, a)
fun inline (t) length arr = primapp Arraylength { t } (arr)*)

                            (*
extern val runtime.no-messages : unit -> unit  @ home = lc_nomessages
extern val alert : string -> unit @ home
*)

datatype 'a option = NONE | SOME of 'a
datatype order = EQUAL | LESS | GREATER

datatype 'a list = nil | :: of 'a * list
infixr ::

(* only works for non-negative numbers now *)
fun stoi s =
    let
        val n = size s
        fun re(acc, i) =
            if i >= n
            then SOME acc
            else let val c = ord (ssub(s, i))
                 in
                     if c >= ord ?0 andalso c <= ord ?9
                     then re(acc * 10 + (c - ord ?0), i + 1)
                     else NONE
                 end
    in
        (* not empty string *)
        if n > 0
        then re(0, 0)
        else NONE
    end


(* standard trick to turn a function into
   a real continuation. *)
(* inline? it probably reduces, usually *)
fun cont (f : unit -> unit) : unit cont =
    letcc ret
    in
        letcc k
        in
            throw k to ret
        end;
        f ();
        primapp Halt { unit cont } ( )
    end

datatype (a, b) sum = LEFT of a | RIGHT of b

fun ignore _ = ()

fun option.map f (SOME x) = SOME (f x)
  | option.map _ NONE = NONE

fun isSome (SOME _) = true
  | isSome NONE = false

fun order.equals (LESS, LESS) = true
  | order.equals (GREATER, GREATER) = true
  | order.equals (EQUAL, EQUAL) = true
  | order.equals (_, _) = false

fun not true = false
  | not false = true

fun o (f, g) x = f(g(x))
infix o

(*

(* install top-level exception handler. *)
val () =
    letcc out
    in
        letcc toplevel
        in
            sethandler_ toplevel;
            throw () to out
        end;

        putc ?u; putc ?n; putc ?c;
        putc ?a; putc ?u; putc ?g;
        putc ?h; putc ?t; putc ? ;
        putc ?e; putc ?x; putc ?n;
        putc ?!; putc ?\n;

        halt ()
    end

(* wrap primitives *)

exception Radix

fun chr n =
    if n < 0 orelse n > 255
    then raise Radix
    else chr_ n

(* arrays *)
exception Subscript

fun sub (a, x) =
    if x < 0 orelse x >= length a
    then raise Subscript
    else sub_(a, x)

fun update (a, x, e) =
    if x < 0 orelse x >= length a
    then raise Subscript
    else update_(a, x, e)

(* numbers *)

exception Div

fun div (a,0) = raise Div
  | div (a,b) = div_ (a,b)

infix div

fun mod (a, b) =
    let val q = a div b
    in
        a - (b * q)
    end

infix mod

*)
*)
