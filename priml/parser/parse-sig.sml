
signature PARSE =
sig
    exception Parse of string

    (* expression parser *)
    val exp : (string * (int * Parsing.associativity)) list ->
                   (EL.exp_ * Pos.pos,Tokens.token) Parsing.parser
    val prog : (string * (int * Parsing.associativity)) list ->
                   (EL.prog,Tokens.token) Parsing.parser

end
