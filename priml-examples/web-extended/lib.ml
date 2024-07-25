open Unix

   (*
let host_compare h1 h2 =
  match (h1, h2) with
  | (ADDR_UNIX s1, ADDR_UNIX s2) -> String.compare s1 s2
  | (ADDR_INET (a1, p1), ADDR_INET (a2, p2)) ->
     String.compare ((string_of_inet_addr a1) ^ (string_of_int p1))
       ((string_of_inet_addr a2) ^ (string_of_int p2))
  | (ADDR_UNIX _, ADDR_INET _) -> -1
  | (ADDR_INET _, ADDR_UNIX _) -> 1
    *)

type host = string
   
let host_compare = String.compare

let host_of_sockaddr h =
  match h with
    ADDR_UNIX s -> s
  | ADDR_INET (a, _) -> string_of_inet_addr a

module TSHashtbl = Hashtbl
module UHashtbl = Hashtbl

type ts_list_hashtbl = (host, float) TSHashtbl.t
type unit_hashtbl = (host, unit) UHashtbl.t

let string_of_host h = h
                         (*
let string_of_host h =
  match h with
    ADDR_UNIX s -> s
  | ADDR_INET (a, p) -> ((string_of_inet_addr a) ^ ":" ^ (string_of_int p))
                          *)
