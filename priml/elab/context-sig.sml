
(* Contexts for elaboration. *)
signature CONTEXT =
sig
    (* what sort of thing (world, type, val), id *)
    exception Absent of string * string
    (* other problems *)
    exception Context of string

    type context

    val empty : context

    val ctol : context -> Layout.layout

    (* lookup operations *)

    (* resolve a value identifier in the current context, return its type and
       status and world *)
    val var : context -> string -> IL.typ IL.poly * Variable.var * IL.idstatus

    (* resolve a type/con identifer in the current context, return its kind
       and binding *)
    val con : context -> string -> IL.kind * IL.con * IL.tystatus

    val prio : context -> string -> IL.prio

    val checkcons : context -> IL.prio -> IL.prio -> bool

    (* has_evar ctx n
       Does the context contain the free type evar n in the type of any
       bound variable?*)
    val has_evar  : context -> int -> bool
    (* same, but for free world evars *)
    val has_wevar : context -> int -> bool


    (* context extension operations *)
    
    (* bind a priority *)
    val bindp : context -> string -> Variable.var -> context
    val bindplab : context -> string -> context

    val bindpcons : context -> IL.prio * IL.prio -> context

    (* bind an identifier to a variable and give that variable 
       the indicated type at the indicated world *)
    val bindv : context -> string -> IL.typ IL.poly -> Variable.var -> context
    (* also idstatus, if not Normal; not necessary to give EL name *)
    val bindex : context -> string option -> IL.typ IL.poly -> Variable.var -> IL.idstatus -> context

    (* bind an identifier to a type constructor with the indicated kind *)
    val bindc : context -> string -> IL.con -> IL.kind -> IL.tystatus -> context

    (* bind a signature to a variable *)
    val bindsig : context -> string -> context -> context

    val plabs : context -> string list
    val pcons : context -> (IL.prio * IL.prio) list

    val install_ne : (unit -> IL.typ) -> unit
end
