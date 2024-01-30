structure IL =
struct

    type intconst = IntConst.intconst

    structure V = Variable
			
    type label = string
    type var = Variable.var
    type id = string

    (* arm in a datatype(sum). might be a carrier ("of
       t") or not. If a carrier, t might be a type
       that is always allocated (e.g., a non-empty
       record) or it might be something we can't
       determine the allocation status of (like a
       type variable). *)
    datatype 'typ arminfo =
      NonCarrier
    | Carrier of { definitely_allocated : bool,
                   carried : 'typ }
      
    fun arminfo_map f NonCarrier = NonCarrier
      | arminfo_map f (Carrier { definitely_allocated, carried }) =
      Carrier { definitely_allocated = definitely_allocated,
                carried = f carried }

    datatype longid =
      Id of id
    | Path of string * longid

    (* existential, for type inference *)
    datatype 'a ebind = (* ? typ *)
        Free of int
      | Bound of 'a

    datatype prio =
      PEvar of prio ebind ref
    | PVar of var
    | PConst of string

    fun prcompare (PEvar (ref (Free _)), _) = LESS
      | prcompare (_, PEvar (ref (Free _))) = GREATER
      | prcompare (PEvar (ref (Bound p1)), p2) = prcompare (p1, p2)
      | prcompare (p1, PEvar (ref (Bound p2))) = prcompare (p1, p2)
      | prcompare (PVar v1, PVar v2) = String.compare (V.show v1, V.show v2)
      | prcompare (PVar v1, PConst c2) = String.compare (V.show v1, c2)
      | prcompare (PConst c1, PVar v2) = String.compare (c1, V.show v2)
      | prcompare (PConst c1, PConst c2) = String.compare (c1, c2)

    structure PrioSet = SplaySetFn (struct 
                                      type ord_key = prio
                                      val compare = prcompare
                                    end)

    structure VM = Variable.Map
    type 'a subst = 'a VM.map
				   
    datatype prioset = 
	     PSEvar of prioset ebind ref
	     | PSSet of PrioSet.set
	     | PSPendSub of exp subst * prioset

    and pconstraint = PCons of prio * prio

    (* types : classifiers for values *)
    and typ =
        TVar of var
      | TRec of (label * typ) list
      (* bool true => total 
         functions are n-ary.
         *)
      | Arrow of bool * (var * typ) list * typ (* FIX: Arrow of bool * (string * typ) list * typ *)
      | Sum of (label * typ arminfo) list
      (* pi_n (mu  v_0 . typ_0
               and v_1 . typ_1
               and ...)
         0 <= n < length l, length l > 0.

         all variables are bound in all arms.

         when unrolling, choose nth arm and
         substitute:

         typ_n [ (pi_0 mu .. and ..) / v_0,
                 (pi_1 mu .. and ..) / v_1,
                 ... ]
         *)
      | Mu of int * (var * typ) list
        (* for elaboration (type inference) *)
      | Evar of typ ebind ref

      | TVec of typ
      | TCont of typ

      | TRef of typ

      | TTag of typ * var

      | Arrows of (bool * (var * typ) list * typ) list  (* FIX: Arrows of (bool * (string * typ) list * typ) list *)

      (* XXX pass ref set constaints through TCmd and TThread. 
       * The correct way to handle this should be a constraint evar and unify
       * them. But this works! (for now) *)
      (* Q: why only one (psconstraint list ref) ? *)
      | TCmd of typ * (prioset * prioset * prioset)
      | TThread of typ * prioset
      | TPrio of prioset (* FIX: make work !!! *)

      (* | TForall of var list * (pconstraint list) * typ (* FIX: delete this *) *)

    (* type constructors. only used in elaboration *)
    and con =
        Typ of typ
      | Lambda of typ list -> typ  (* FIX: Lambda of (string * typ) list -> typ *)

    (* polymorphic type *) 
    and 'a poly = Poly of { (* prios : var list, *) (* FIX: delete prios *)
                            tys    : var list } * 'a

    and value = (* FIX: delete prios *)
        Polyvar  of { tys : typ list, (* prios : prio list, *)
                      var : var }
      | Polyuvar of { tys : typ list, (* prios : prio list, *)
                      var : var }
      | MLVal of string
      | Int of intconst
      | String of string
      | Prio of prio
      | VRecord of (label * value) list
      | VRoll of typ * value
      | VInject of typ * label * value option

      | Fns of 
        { name : var,
          arg  : var list,
          dom  : typ list,
          cod  : typ,
          body : exp,
          (* should always inline? *)
          inline : bool,
          (* these may be conservative estimates *)
          recu : bool,
          total : bool } list

      (* select one of the functions in a bundle *)
      | FSel of int * value

      (* | PFn of
        { pname  : var,
          parg   : var list,
          pconst : pconstraint list,
          pcod   : typ,
          pbody  : exp } (* FIX: delete this *) *)
      | PCmd of prioset * typ * cmd

    and exp =
        Value of value
      
      (* application is n-ary *)
      | App of exp * exp list

      | Record of (label * exp) list
      (* #lab/typ e *)
      | Proj of label * typ * exp
      | Raise of typ * exp
      (* var bound to exn value within handler*)
      | Handle of exp * typ * var * exp

      | Seq of exp * exp
      | Let of dec * exp * typ
      | Unroll of exp
      | Roll of typ * exp

      (* tag v with t *)
      | Tag of exp * exp

      | Untag of { typ : typ,
                   obj : exp,
                   target : exp,
                   bound : var, (* within yes *)
                   yes : exp,
                   no : exp }

      (* apply a primitive to some expressions and types *)
      | Primapp of Primop.primop * exp list * typ list

      (* sum type, object, var (for all arms but not default), 
         branches, default, return type.
         the label/exp list need not be exhaustive.
         *)
      | Sumcase of typ * exp * var * (label * exp) list * exp * typ

      (* simpler; no inner val needs to be defined. can't be exhaustive. *)
      | Intcase of exp * (intconst * exp) list * exp * typ

      | Inject of typ * label * exp option
      | Cmd of prioset * cmd
      (* | PFApp of exp * prio (* FIX: delete this *) *)
    (*
      (* for more efficient treatment of blobs of text. *)
      | Jointext of exp list
*)
    and cmd =
        Bind of var * exp * cmd
      | Spawn of exp * typ * cmd
      | Sync of exp
      | Poll of exp
      | Cancel of exp
      | Ret of exp
      | Change of exp

    and dec =
        Do of exp
        (* XXX5 cleanup: should have Val binding that takes an
           expression, then all the rest just take values for
           generalization purposes. *)
        (* quantifiers on the outside -- no poly recursion *)
        (* XXX5 could make PolyVal that requires syntactic value.. *)
      | Val of (var * typ * exp) poly
      | Tagtype of var
        (* tag of typ in tagtype *)
      | Newtag of var * typ * var
      | Priority of var

    (* the kind is the number of curried arguments. 0 is kind T. *)
    withtype kind = int

                (* declarations, priorities, constraints, fairness criteria, main *)
    type prog = dec list * string list * (string * string) list *
                (string * intconst) list * cmd

    (* now a derived form *)
    fun Var v = Polyvar { tys = nil, (* prios = nil, *)
                          var = v }
    (* expand to linear search *)
    fun Tagcase (t, obj, bound, vel, def, rett) = 
      let
        val vo = Variable.namedvar "tagcase"
        fun go nil = def
          | go ((v : value, e) :: rest) =
          Untag { typ = t,
                  obj = Value (Var vo),
                  target = Value v,
                  bound = bound,
                  yes = e,
                  no = go rest }
      in
        Let (Val (Poly ({tys=nil}, (vo, t, obj))),
             go vel,
	     rett)
      end

    fun pr_eq (PConst s1, PConst s2) = (case String.compare (s1, s2) of
                                            EQUAL => true
                                          | _ => false)
      | pr_eq (PVar v1, PVar v2) = (case String.compare (V.show v1, V.show v2) of
                                            EQUAL => true
                                          | _ => false)
      | pr_eq (PVar v1, PConst s2) = (case String.compare (V.show v1, s2) of
                                            EQUAL => true
                                          | _ => false)
      | pr_eq (PConst c1, PVar v2) = (case String.compare (c1, V.show v2) of
                                            EQUAL => true
                                          | _ => false)
      | pr_eq _ = false

    datatype tystatus = Regular | Extensible
    datatype idstatus = 
        Normal 
      | Constructor 
      (* the value is the tag, in scope, that should be used
         to deconstruct this tagged expression *)
      | Tagger of value
      | Primitive of Primop.primop

end
