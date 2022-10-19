
(* The type of tokens. *)

type token = 
  | WITH
  | WILDCARD
  | VAL
  | UNIT
  | UID of (string)
  | TYPE
  | SYNTH
  | STR of (string)
  | STAR
  | SIG
  | SEMI
  | SATISFYING
  | RPAREN
  | RBRACKET
  | PIPE
  | OF
  | NEQ
  | MU
  | MATCH
  | LPAREN
  | LID of (string)
  | LET
  | LBRACKET
  | INT of (int)
  | INCLUDE
  | FUN
  | FORALL
  | FIX
  | FATEQ
  | EQUIV
  | EQ
  | EOF
  | END
  | DOT
  | COMMA
  | COLON
  | BINDING
  | ARR

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val unprocessed_problem: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Problem.t_unprocessed)

val imports_decls_start: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (string list * Declaration.t list)

val exp: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Lang.Expr.t)
