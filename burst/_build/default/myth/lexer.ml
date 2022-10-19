# 1 "myth/lexer.mll"
 
open Lexing
open Parser

exception Lexer_error of string

let reserved_words : (string * Parser.token) list =
  [ ("fun", FUN)
  ; ("match", MATCH)
  ; ("with", WITH)
  ; ("type", TYPE)
  ; ("of", OF)
  ; ("let", LET)
  ; ("in", IN)
  ; ("rec", REC)
  ; ("unit", UNIT)
  ]

let symbols : (string * Parser.token) list =
  [ ("?", HOLE)
  ; ("|>", IMPLIES)
  ; ("=", EQ)
  ; ("->", ARR)
  ; ("=>", FATARR)
  ; (".", DOT)
  ; (",", COMMA)
  ; (":", COLON)
  ; (";", SEMI)
  ; ("*", STAR)
  ; ("|", PIPE)
  ; ("(", LPAREN)
  ; (")", RPAREN)
  ; ("{", LBRACE)
  ; ("}", RBRACE)
  ; ("[", LBRACKET)
  ; ("]", RBRACKET)
  ; ("_", UNDERSCORE)
  ]

let create_token lexbuf =
  let str = lexeme lexbuf in
  match Util.lookup str reserved_words with
  | None   -> LID str
  | Some t -> t

let create_symbol lexbuf =
  let str = lexeme lexbuf in
  match Util.lookup str symbols with
  | None   -> raise @@ Lexer_error ("Unexpected token: " ^ str)
  | Some t -> t

let create_proj lexbuf =
  let str = lexeme lexbuf in
  let len = String.length str in
  PROJ (int_of_string (String.sub str 1 (len - 1)))

# 59 "myth/lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\247\255\248\255\000\000\002\000\030\000\078\000\160\000\
    \001\000\002\000\007\000\001\000\235\000\254\255\255\255\245\000\
    \252\255\129\000\251\255\252\255\253\255\005\000\019\000\255\255\
    \254\255";
  Lexing.lex_backtrk =
   "\255\255\255\255\255\255\008\000\007\000\007\000\006\000\005\000\
    \004\000\004\000\004\000\007\000\008\000\255\255\255\255\002\000\
    \255\255\255\255\255\255\255\255\255\255\002\000\002\000\255\255\
    \255\255";
  Lexing.lex_default =
   "\001\000\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\000\000\000\000\255\255\
    \000\000\020\000\000\000\000\000\000\000\255\255\255\255\000\000\
    \000\000";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\010\000\009\000\009\000\009\000\008\000\008\000\008\000\
    \010\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \010\000\000\000\000\000\012\000\000\000\000\000\000\000\010\000\
    \011\000\002\000\002\000\016\000\002\000\003\000\002\000\024\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\002\000\002\000\023\000\004\000\002\000\002\000\
    \002\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\002\000\002\000\002\000\000\000\002\000\
    \000\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\002\000\005\000\002\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \000\000\000\000\000\000\019\000\000\000\000\000\000\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\021\000\000\000\022\000\000\000\006\000\000\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\000\000\000\000\000\000\000\000\007\000\
    \014\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\015\000\015\000\015\000\015\000\015\000\
    \015\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\
    \015\000\015\000\015\000\015\000\015\000\015\000\015\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\018\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\008\000\009\000\000\000\008\000\009\000\
    \010\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\000\000\255\255\255\255\255\255\010\000\
    \000\000\000\000\000\000\011\000\000\000\000\000\000\000\021\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\022\000\000\000\003\000\000\000\
    \004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\005\000\000\000\255\255\000\000\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \255\255\255\255\255\255\017\000\255\255\255\255\255\255\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\017\000\255\255\017\000\255\255\006\000\255\255\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\255\255\255\255\255\255\255\255\007\000\
    \000\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\012\000\012\000\012\000\012\000\012\000\
    \012\000\012\000\012\000\012\000\012\000\015\000\015\000\015\000\
    \015\000\015\000\015\000\015\000\015\000\015\000\015\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\017\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255";
  Lexing.lex_base_code =
   "";
  Lexing.lex_backtrk_code =
   "";
  Lexing.lex_default_code =
   "";
  Lexing.lex_trans_code =
   "";
  Lexing.lex_check_code =
   "";
  Lexing.lex_code =
   "";
}

let rec token lexbuf =
   __ocaml_lex_token_rec lexbuf 0
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 66 "myth/lexer.mll"
          ( EOF )
# 225 "myth/lexer.ml"

  | 1 ->
# 67 "myth/lexer.mll"
          ( INT (int_of_string (lexeme lexbuf)) )
# 230 "myth/lexer.ml"

  | 2 ->
# 68 "myth/lexer.mll"
               ( create_proj lexbuf )
# 235 "myth/lexer.ml"

  | 3 ->
# 69 "myth/lexer.mll"
         (comments 0 lexbuf)
# 240 "myth/lexer.ml"

  | 4 ->
# 70 "myth/lexer.mll"
                              ( token lexbuf )
# 245 "myth/lexer.ml"

  | 5 ->
# 71 "myth/lexer.mll"
                                         ( create_token lexbuf )
# 250 "myth/lexer.ml"

  | 6 ->
# 72 "myth/lexer.mll"
                                         ( UID (lexeme lexbuf) )
# 255 "myth/lexer.ml"

  | 7 ->
# 75 "myth/lexer.mll"
    ( create_symbol lexbuf )
# 260 "myth/lexer.ml"

  | 8 ->
let
# 76 "myth/lexer.mll"
         c
# 266 "myth/lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 76 "myth/lexer.mll"
           ( raise @@ Lexer_error ("Unexpected character: " ^ Char.escaped c) )
# 270 "myth/lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_token_rec lexbuf __ocaml_lex_state

and comments level lexbuf =
   __ocaml_lex_comments_rec level lexbuf 17
and __ocaml_lex_comments_rec level lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 79 "myth/lexer.mll"
         ( if level = 0 then token lexbuf
	   else comments (level-1) lexbuf )
# 283 "myth/lexer.ml"

  | 1 ->
# 81 "myth/lexer.mll"
         ( comments (level+1) lexbuf)
# 288 "myth/lexer.ml"

  | 2 ->
# 82 "myth/lexer.mll"
             ( comments level lexbuf )
# 293 "myth/lexer.ml"

  | 3 ->
# 83 "myth/lexer.mll"
         ( comments level lexbuf )
# 298 "myth/lexer.ml"

  | 4 ->
# 84 "myth/lexer.mll"
         ( failwith "Comments are not closed" )
# 303 "myth/lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_comments_rec level lexbuf __ocaml_lex_state

;;
