signature ELABUTIL =
sig

    exception Elaborate of string

    val ltos : Pos.pos -> string

    val error : Pos.pos -> string -> 'b

    (* unify context location message actual expected *)
    val unify : Context.context -> Pos.pos -> string -> 
                    IL.typ -> IL.typ -> unit

    (* supertype context location message actual expected *)
					    (*
    val supertype : Context.context -> Pos.pos -> string -> 
                    IL.typ -> IL.typ -> unit
					    *)

    (* val unifyp : Context.context -> Pos.pos -> string -> 
                    IL.prio -> IL.prio -> unit *)

					    (*
    (* check_constraint context location p1 <= p2 *)
    val check_constraint : Context.context -> Pos.pos ->
                           IL.prio -> IL.prio -> unit
					    *)
					    
    (* int to string *)
    val itos : int -> string

    (* also consider using IL.CompileWarn expression *)
    val warn : Pos.pos -> string -> unit

    (* generate a new string with arg as base *)
    val newstr : string -> string

    (* polygen sctx t atworld
       
       perform polymorphic generalization on a type, for
       both types and worlds.

       If t has unset type or world evars that do not appear
       anywhere in the context sctx, then they will be
       generalized. We never generalize the atworld, because
       that cannot be forall-quantified. Instead use polywgen 
       below.

       returns a new generalized type along with the bound
       type variables and world variables. *)
    val polygen : Context.context -> IL.typ -> (* IL.prio ->  *)
                        { t : IL.typ, 
                          tl : Variable.var list }

    (* polygen sctx w

       If the world is an unbound evar that can be safely generalized (see above), 
       then instantiate it and return the new variable. Otherwise, return NONE. *)
    val polywgen : Context.context -> IL.prio -> Variable.var option

    (* instantiate all of the bound type and world variables with new evars and wevars;
       return the types and worlds used to instantiate the type *)
    val evarize : IL.typ IL.poly -> IL.typ * IL.typ list
    (* same, but list of types (result will have the same length) *)
    val evarizes : IL.typ list IL.poly -> IL.typ list * IL.typ list

(*
    val psubst1 : IL.prio -> Variable.var -> IL.typ -> IL.typ
    val psubsc1 : IL.prio -> Variable.var -> IL.pconstraint -> IL.pconstraint
*)
    val psesubst : IL.typ -> IL.typ

    val unroll : Pos.pos -> IL.typ -> IL.typ

    val mono : 'a -> 'a IL.poly

(*
    (* call this to clear the mobile check queue *)
    val clear_mobile : unit -> unit

    (* require that the type be mobile. If the type is not
       yet determined, then it will be placed in a queue to
       check after elaboration has finished. *)
    val require_mobile : Context.context -> Pos.pos -> string -> IL.typ -> unit

    val check_mobile : unit -> unit
*)

    val ptoil : Podata.potype -> IL.typ

end
