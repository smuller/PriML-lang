val bot = Thread.bot


val w1 = (Thread.new ())


val w2 = (Thread.new ())


val w3 = (Thread.new ())


val _ = ((Thread.new_lessthan w1) w2)


val _ = ()


fun  foo (x : int)  =  x


fun 
f
()
 :  int
 = 
    (let
	 val t = ((Thread.spawn (let fun  anonfn _  =  42 in anonfn end)) w2)
	 val x = (Thread.sync t)
     in
	 x
     end)


val
_
=
(let
     val a = ((Thread.spawn (let fun  anonfn _  =  42 in anonfn end)) w2)
     val x = f
     val z = 21
 in
     (foo z)
 end)