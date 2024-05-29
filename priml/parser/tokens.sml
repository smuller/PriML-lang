
structure Tokens =
struct

    (* print[hello [b[world]]!] 

       lexes as

       ID "print"
       TEXT [STR "hello ",
             EXP (ID "b" :: TEXT [STR "world"])
             STR "!"]

       *)

    datatype token =
        ID of string
      | STR of string
      | PRIO of string
      | INT of IntConst.intconst
      | CHAR of char
      | FLOAT of real
      | BAD of char
      | UNIT
      | FN
      | LET
      | IN
      | OP
      | OPEN
      | END
      | CASE
      | OF
      | AS
      | ELSE
      | IF
      | THEN
      | TIMES
      | DIVIDE
      | HASH
      | DO
      | VAL
      | AND
      | FUN
      | TYPE
      | DATATYPE
      | DERIVING
      | EXCEPTION
      | VEXCEPTION
      | HANDLE
      | TAGTYPE
      | NEWTAG
      | NEWVTAG
      | ANDALSO
      | ANDTHEN
      | ORELSE
      | OTHERWISE
      | INFIX
      | INFIXR
      | NONFIX
      | STRUCTURE
      | STRUCT
      | LIBRARY
      | LIB
      | SIGNATURE
      | SIG
      | COLONGREATER
      | DOT
      | LPAREN
      | RPAREN
      | DARROW
      | ARROW
      | COLON
      | SEMICOLON
      | LBRACE
      | RAISE
      | RBRACE
      | BAR
      | UNDERSCORE
      | EQUALS
      | COMMA
      | IMPORT
      | DATAFILE

      | PRIMAPP
      | INLINE

      (* PrioML-specific *)
(*       | WFUN *)
      | PRIORITY
      | ORDER
      | WFN
      | FAIRNESS

      | LESSTHAN
      | LESSEQUAL
      | CAND

      | SPAWN
      | SYNC
      | POLL
      | CANCEL
      | LSQUARE
      | RSQUARE
      | LARROW
      | RET
      | CHANGE

      | CMD
      | MAIN

      | THREAD
      | FORALL

      | EXTERN

      | NEWMUTEX
      | WITHMUTEX
	
(*
      (* ML5-specific *)
      | EXPORT
      | GET
      | PUT
      | AT
      | FROM
      | WORLD
      | TILDE
      | ADDR
      | UNIT
      | HOLD
      | LETA
      | LETSHAM
      | SHAM

      | JAVASCRIPT
      | BYTECODE

      | LETCC
      | THROW
      | TO
      | SAY
*)

    (* only for "basic" tokens, not constant-wrappers *)
    fun eq (FN, FN) = true
      | eq (LET, LET) = true
      | eq (IN, IN) = true
      | eq (END, END) = true
      | eq (CASE, CASE) = true
      | eq (OF, OF) = true
      | eq (OPEN, OPEN) = true
      | eq (AS, AS) = true
      | eq (ELSE, ELSE) = true
      | eq (IF, IF) = true
      | eq (THEN, THEN) = true
      | eq (TIMES, TIMES) = true
      | eq (DIVIDE, DIVIDE) = true
      | eq (HASH, HASH) = true
      | eq (DO, DO) = true
      | eq (UNIT, UNIT) = true
      | eq (VAL, VAL) = true
      | eq (AND, AND) = true
      | eq (FUN, FUN) = true
      | eq (TYPE, TYPE) = true
      | eq (DATATYPE, DATATYPE) = true
      | eq (EXCEPTION, EXCEPTION) = true
      | eq (VEXCEPTION, VEXCEPTION) = true
      | eq (HANDLE, HANDLE) = true
      | eq (TAGTYPE, TAGTYPE) = true
      | eq (NEWTAG, NEWTAG) = true
      | eq (NEWVTAG, NEWVTAG) = true
      | eq (ANDALSO, ANDALSO) = true
      | eq (ANDTHEN, ANDTHEN) = true
      | eq (ORELSE, ORELSE) = true
      | eq (OTHERWISE, OTHERWISE) = true
      | eq (INFIX, INFIX) = true
      | eq (INFIXR, INFIXR) = true
      | eq (NONFIX, NONFIX) = true
      | eq (STRUCTURE, STRUCTURE) = true
      | eq (STRUCT, STRUCT) = true
      | eq (LIBRARY, LIBRARY) = true
      | eq (LIB, LIB) = true
      | eq (SIGNATURE, SIGNATURE) = true
      | eq (SIG, SIG) = true
      | eq (COLONGREATER, COLONGREATER) = true
      | eq (RAISE, RAISE) = true
      | eq (DOT, DOT) = true
      | eq (LPAREN, LPAREN) = true
      | eq (RPAREN, RPAREN) = true
      | eq (DARROW, DARROW) = true
      | eq (ARROW, ARROW) = true
      | eq (COLON, COLON) = true
      | eq (SEMICOLON, SEMICOLON) = true
      | eq (LBRACE, LBRACE) = true
      | eq (RBRACE, RBRACE) = true
      | eq (OP, OP) = true
      | eq (BAR, BAR) = true
      | eq (UNDERSCORE, UNDERSCORE) = true
      | eq (DERIVING, DERIVING) = true
      | eq (EQUALS, EQUALS) = true
      | eq (COMMA, COMMA) = true
      | eq (IMPORT, IMPORT) = true
      | eq (DATAFILE, DATAFILE) = true
      | eq (PRIMAPP, PRIMAPP) = true
      | eq (INLINE, INLINE) = true
(*      | eq (WFUN, WFUN) = true *)
      | eq (PRIORITY, PRIORITY) = true
      | eq (ORDER, ORDER) = true
      | eq (FAIRNESS, FAIRNESS) = true
      | eq (EXTERN, EXTERN) = true
      | eq (SPAWN, SPAWN) = true
      | eq (SYNC, SYNC) = true
      | eq (POLL, POLL) = true
      | eq (CANCEL, CANCEL) = true
      | eq (LSQUARE, LSQUARE) = true
      | eq (RSQUARE, RSQUARE) = true
      | eq (LARROW, LARROW) = true
      | eq (RET, RET) = true
      | eq (CHANGE, CHANGE) = true
      | eq (CMD, CMD) = true
      | eq (FORALL, FORALL) = true
      | eq (THREAD, THREAD) = true
      | eq (LESSTHAN, LESSTHAN) = true
      | eq (LESSEQUAL, LESSEQUAL) = true
      | eq (MAIN, MAIN) = true
      | eq (NEWMUTEX, NEWMUTEX) = true
      | eq (WITHMUTEX, WITHMUTEX) = true
      | eq _ = false

end
