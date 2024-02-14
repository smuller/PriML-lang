fun le (a, b) = a <= b
fun lt (a, b) = a < b
fun gt (a, b) = a > b
fun eq (a, b) = a = b
fun minus (a, b) = a - b
fun plus (a, b) = a + b
fun mult (a, b) = a * b
fun cat (a, b) = a ^ b
fun upd (a, b) = a := b
fun cons (a, b) = a :: b
fun dv (a, b) = Int.div (a, b)
fun slt (a, b) = String.< (a, b)

structure Priority =
struct
type t = int

val bot = 1

val ctr = ref 2

fun top () = !ctr + 1

fun new () =
    !ctr
    before (ctr := (!ctr) + 1)

fun new_lessthan p1 p2 =
    ()
end

structure Basic =
struct
fun init () = ()
fun initPriorities () = ()
fun finalizePriorities () = ()
end

structure Thread =
struct
type 'a t = 'a

fun spawn f p = f ()
fun sync v = v
fun poll v = SOME v
fun change p = ()
fun cancel _ = ()
end
	    
	
