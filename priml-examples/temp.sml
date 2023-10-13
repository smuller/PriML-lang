val A = (Priority.new ())

val B = (Priority.new ())

val bot = Priority.bot

val _ = (Basic.initPriorities ())

val _ = ((Priority.new_lessthan bot) A)

val _ = ((Priority.new_lessthan bot) B)

val _ = ((Priority.new_lessthan A) (Priority.top ()))

val _ = ((Priority.new_lessthan B) (Priority.top ()))

val _ = ((Priority.new_lessthan bot) (Priority.top ()))

val _ = (Basic.finalizePriorities ())

val _ = (Basic.init ())

val
_
=
(let
     fun  anonfn _  =  (let val x = A in (if  true  then x else B) end)
 in
     anonfn
 end)