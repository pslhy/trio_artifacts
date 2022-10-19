
(* The type of tokens. *)

type token = 
  | WITH
  | UNIT
  | UNDERSCORE
  | UID of (string)
  | TYPE
  | STAR
  | SEMI
  | RPAREN
  | REC
  | RBRACKET
  | RBRACE
  | PROJ of (int)
  | PIPE
  | OF
  | MATCH
  | LPAREN
  | LID of (string)
  | LET
  | LBRACKET
  | LBRACE
  | INT of (int)
  | IN
  | IMPLIES
  | HOLE
  | FUN
  | FATARR
  | EQ
  | EOF
  | DOT
  | COMMA
  | COLON
  | ARR

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Lang.prog)

val decls: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Lang.decl list)
