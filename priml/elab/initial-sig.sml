
(* The initial context. *)

signature INITIAL =
sig

    val ilint : IL.typ
    val ilchar : IL.typ
    val ilstring : IL.typ
    val ilexn : IL.typ
    val ilbool : IL.typ

    (* these are abstract type variables *)
    val intvar : Variable.var
    val charvar : Variable.var
    val stringvar : Variable.var
    val exnvar : Variable.var

    val initial : Context.context
    val botname : string
    val bot : IL.prio

    (* wrap with declarations and imports needed 
       by the compiler (bool, exceptions) *)
     val wrap : EL.prog -> EL.prog

    val trueexp  : Pos.pos -> EL.exp
    val falseexp : Pos.pos -> EL.exp

    val trueexpil  : IL.exp
    val falseexpil : IL.exp

    val truepat  : EL.pat
    val falsepat : EL.pat

    val matchname : string
    (* value of exception Match *)
    val matchexp : Pos.pos -> EL.exp

    val boolname : string
    val truename : string
    val falsename : string
    val exnname : string
    val eventname : string
(*  val listname : string *)

end
