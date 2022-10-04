
structure IL =
struct

    type intconst = IntConst.intconst

    type label = string
    type var = Variable.var

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


    datatype prio =
      PEvar of prio ebind ref
    | PVar of var
    | PConst of string

    and pconstraint = PCons of prio * prio

    (* types : classifiers for values *)
    and typ =
        TVar of var
      | TRec of (label * typ) list
      (* bool true => total
         functions are n-ary.
         *)
      | Arrow of bool * typ list * typ
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

      | Arrows of (bool * typ list * typ) list

      | TCmd of typ * prio
      | TThread of typ * prio
      | TForall of var list * (pconstraint list) * typ

    (* type constructors. only used in elaboration *)
    and con =
        Typ of typ
      | Lambda of typ list -> typ

    (* existential, for type inference *)
    and 'a ebind =
        Free of int
      | Bound of 'a

    (* polymorphic type *)
    and 'a poly = Poly of { prios : var list,
                            tys    : var list } * 'a

    and value =
        Polyvar  of { tys : typ list, prios : prio list, var : var }
      | Polyuvar of { tys : typ list, prios : prio list, var : var }
      | MLVal of string
      | Int of intconst
      | String of string
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

      | PFn of
        { pname  : var,
          parg   : var list,
          pconst : pconstraint list,
          pcod   : typ,
          pbody  : exp }
      | PCmd of prio * typ * cmd

    and exp =
        Value of value

      (* application is n-ary *)
      | App of exp * exp list

      | Record of (label * exp) list
      (* #lab/typ e *)
      | Proj of label * typ * exp
      | Raise of typ * exp
      (* var bound to exn value within handler *)
      | Handle of exp * typ * var * exp

      | Seq of exp * exp
      | Let of dec * exp
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
         branches, default.
         the label/exp list need not be exhaustive.
         *)
      | Sumcase of typ * exp * var * (label * exp) list * exp

      (* simpler; no inner val needs to be defined. can't be exhaustive. *)
      | Intcase of exp * (intconst * exp) list * exp

      | Inject of typ * label * exp option
      | Cmd of prio * cmd
      | PFApp of exp * prio
    (*
      (* for more efficient treatment of blobs of text. *)
      | Jointext of exp list
*)
    and cmd =
        Bind of var * exp * cmd
      | Spawn of prio * typ * cmd
      | Sync of exp
      | Poll of exp
      | Cancel of exp
      | Ret of exp

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

    (* the kind is the number of curried arguments. 0 is kind T. *)
    withtype kind = int

                (* declarations, priorities, constraints, fairness criteria, main *)
    type prog = dec list * string list * (string * string) list *
                (string * intconst) list * cmd

    (* now a derived form *)
    fun Var v = Polyvar { tys = nil, prios = nil, var = v }
    (* expand to linear search *)
    fun Tagcase (t, obj, bound, vel, def) =
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
        Let (Val (Poly ({prios=nil, tys=nil}, (vo, t, obj))),
             go vel)
      end

    fun pr_eq (PConst s1, PConst s2) = (case String.compare (s1, s2) of
                                            EQUAL => true
                                          | _ => false)
      | pr_eq (PVar v1, PVar v2) = Variable.eq (v1, v2)
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
