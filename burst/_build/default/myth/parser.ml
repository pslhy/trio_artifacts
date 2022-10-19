
module MenhirBasics = struct
  
  exception Error
  
  let _eRR : exn =
    Error
  
  type token = 
    | WITH
    | UNIT
    | UNDERSCORE
    | UID of (
# 21 "myth/parser.mly"
       (string)
# 17 "myth/parser.ml"
  )
    | TYPE
    | STAR
    | SEMI
    | RPAREN
    | REC
    | RBRACKET
    | RBRACE
    | PROJ of (
# 22 "myth/parser.mly"
       (int)
# 29 "myth/parser.ml"
  )
    | PIPE
    | OF
    | MATCH
    | LPAREN
    | LID of (
# 20 "myth/parser.mly"
       (string)
# 38 "myth/parser.ml"
  )
    | LET
    | LBRACKET
    | LBRACE
    | INT of (
# 24 "myth/parser.mly"
       (int)
# 46 "myth/parser.ml"
  )
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
  
end

include MenhirBasics

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState267
  | MenhirState265
  | MenhirState256
  | MenhirState251
  | MenhirState248
  | MenhirState243
  | MenhirState241
  | MenhirState235
  | MenhirState228
  | MenhirState225
  | MenhirState222
  | MenhirState219
  | MenhirState215
  | MenhirState213
  | MenhirState211
  | MenhirState208
  | MenhirState205
  | MenhirState203
  | MenhirState200
  | MenhirState197
  | MenhirState196
  | MenhirState192
  | MenhirState186
  | MenhirState184
  | MenhirState183
  | MenhirState179
  | MenhirState177
  | MenhirState176
  | MenhirState170
  | MenhirState166
  | MenhirState160
  | MenhirState155
  | MenhirState152
  | MenhirState148
  | MenhirState143
  | MenhirState139
  | MenhirState137
  | MenhirState130
  | MenhirState127
  | MenhirState123
  | MenhirState121
  | MenhirState119
  | MenhirState118
  | MenhirState117
  | MenhirState114
  | MenhirState110
  | MenhirState108
  | MenhirState102
  | MenhirState94
  | MenhirState92
  | MenhirState88
  | MenhirState86
  | MenhirState84
  | MenhirState82
  | MenhirState81
  | MenhirState80
  | MenhirState78
  | MenhirState77
  | MenhirState76
  | MenhirState71
  | MenhirState70
  | MenhirState69
  | MenhirState67
  | MenhirState64
  | MenhirState62
  | MenhirState59
  | MenhirState56
  | MenhirState55
  | MenhirState46
  | MenhirState38
  | MenhirState36
  | MenhirState33
  | MenhirState30
  | MenhirState19
  | MenhirState16
  | MenhirState14
  | MenhirState10
  | MenhirState8
  | MenhirState0

# 1 "myth/parser.mly"
  
open Lang

let rec ctor_of_int (n:int) : exp =
  if n = 0
  then ECtor("O", EUnit)
  else ECtor("S", ctor_of_int (n-1))

let rec list_of_exps (l:exp list) : exp =
  match l with
  | [] -> ECtor("Nil", EUnit)
  | e::es -> ECtor("Cons", ETuple [e; (list_of_exps es)])

let rec appify (e:exp) (es:exp list) : exp =
  match es with
  | [] -> e
  | e'::es -> appify (EApp (e, e')) es

# 171 "myth/parser.ml"

let rec _menhir_goto_pattern_list_one : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.pattern list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LID _v ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
        | LPAREN ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | UNDERSCORE ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState155)
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (p : (Lang.pattern))), _, (ps : (Lang.pattern list))) = _menhir_stack in
        let _v : (Lang.pattern) = 
# 296 "myth/parser.mly"
    ( PTuple (p :: List.rev ps) )
# 205 "myth/parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_record_patterns : _menhir_env -> 'ttv_tail -> ((string * Lang.pattern) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), (ps : ((string * Lang.pattern) list))) = _menhir_stack in
        let _v : (Lang.pattern) = 
# 298 "myth/parser.mly"
    ( PRcd (List.rev ps) )
# 230 "myth/parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
    | SEMI ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | EQ ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LBRACE ->
                    _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState148
                | LID _v ->
                    _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _v
                | LPAREN ->
                    _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState148
                | UNDERSCORE ->
                    _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState148
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState148)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_pattern : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.pattern) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, (l : (
# 20 "myth/parser.mly"
       (string)
# 288 "myth/parser.ml"
        ))), _, (p : (Lang.pattern))) = _menhir_stack in
        let _v : ((string * Lang.pattern) list) = 
# 308 "myth/parser.mly"
    ( [(l,p)] )
# 293 "myth/parser.ml"
         in
        _menhir_goto_record_patterns _menhir_env _menhir_stack _v
    | MenhirState148 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, (ps : ((string * Lang.pattern) list))), (l : (
# 20 "myth/parser.mly"
       (string)
# 302 "myth/parser.ml"
        ))), _, (p : (Lang.pattern))) = _menhir_stack in
        let _v : ((string * Lang.pattern) list) = 
# 310 "myth/parser.mly"
    ( (l,p) :: ps )
# 307 "myth/parser.ml"
         in
        _menhir_goto_record_patterns _menhir_env _menhir_stack _v
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState152
            | LID _v ->
                _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _v
            | LPAREN ->
                _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState152
            | UNDERSCORE ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState152
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState152)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState155 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (ps : (Lang.pattern list))), _, (p : (Lang.pattern))) = _menhir_stack in
        let _v : (Lang.pattern list) = 
# 304 "myth/parser.mly"
    ( p::ps )
# 345 "myth/parser.ml"
         in
        _menhir_goto_pattern_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState152 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (p : (Lang.pattern))) = _menhir_stack in
        let _v : (Lang.pattern list) = 
# 302 "myth/parser.mly"
    ( [p] )
# 355 "myth/parser.ml"
         in
        _menhir_goto_pattern_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState137 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, (c : (
# 21 "myth/parser.mly"
       (string)
# 364 "myth/parser.ml"
        ))), _, (p : (Lang.pattern))) = _menhir_stack in
        let _v : (Lang.pat) = 
# 286 "myth/parser.mly"
    ( (c, Some p) )
# 369 "myth/parser.ml"
         in
        _menhir_goto_pat _menhir_env _menhir_stack _v
    | _ ->
        _menhir_fail ()

and _menhir_run251 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.exp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FUN ->
        _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState251
    | INT _v ->
        _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _v
    | LBRACE ->
        _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState251
    | LBRACKET ->
        _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState251
    | LID _v ->
        _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _v
    | LPAREN ->
        _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState251
    | UID _v ->
        _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState251

and _menhir_goto_pat : _menhir_env -> 'ttv_tail -> (Lang.pat) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FUN ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState160
        | INT _v ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _v
        | LBRACE ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState160
        | LBRACKET ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState160
        | LET ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState160
        | LID _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _v
        | LPAREN ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState160
        | MATCH ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState160
        | PROJ _v ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _v
        | UID _v ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState160)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run138 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (Lang.pattern) = 
# 292 "myth/parser.mly"
    ( PWildcard )
# 448 "myth/parser.ml"
     in
    _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v

and _menhir_run139 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | LID _v ->
        _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
    | LPAREN ->
        _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | UNDERSCORE ->
        _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState139

and _menhir_run140 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 20 "myth/parser.mly"
       (string)
# 474 "myth/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (x : (
# 20 "myth/parser.mly"
       (string)
# 482 "myth/parser.ml"
    )) = _v in
    let _v : (Lang.pattern) = 
# 294 "myth/parser.mly"
    ( PVar x )
# 487 "myth/parser.ml"
     in
    _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v

and _menhir_run141 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | LID _v ->
                _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
            | LPAREN ->
                _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | UNDERSCORE ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run130 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.exp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FUN ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | INT _v ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
    | LBRACE ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | LBRACKET ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | LET ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | LID _v ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
    | LPAREN ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | MATCH ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | PROJ _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
    | UID _v ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState130

and _menhir_run100 : _menhir_env -> 'ttv_tail * _menhir_state * ((string * Lang.exp) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState102
            | INT _v ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
            | LBRACE ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState102
            | LBRACKET ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState102
            | LET ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState102
            | LID _v ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
            | LPAREN ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState102
            | MATCH ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState102
            | PROJ _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
            | UID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState102)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_evidencelist_one : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMI ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FUN ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState267
        | INT _v ->
            _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState267 _v
        | LBRACE ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState267
        | LBRACKET ->
            _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState267
        | LID _v ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState267 _v
        | LPAREN ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState267
        | UID _v ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState267 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState267)
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (v : (Lang.exp))), _, (vs : (Lang.exp list))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 406 "myth/parser.mly"
    ( v :: List.rev vs )
# 651 "myth/parser.ml"
         in
        _menhir_goto_evidencelist _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_ev_val_list_one : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState248 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run251 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (v : (Lang.exp))), _, (vs : (Lang.exp list))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 370 "myth/parser.mly"
    ( ETuple (v:: List.rev vs) )
# 680 "myth/parser.ml"
             in
            _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState256 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run251 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (c : (
# 21 "myth/parser.mly"
       (string)
# 703 "myth/parser.ml"
            ))), _, (v : (Lang.exp))), _, (vs : (Lang.exp list))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 358 "myth/parser.mly"
    ( ECtor (c, ETuple (v :: List.rev vs)) )
# 708 "myth/parser.ml"
             in
            _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_ev_val_semi_list_one : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMI ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FUN ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | INT _v ->
            _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
        | LBRACE ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | LBRACKET ->
            _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | LID _v ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
        | LPAREN ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | UID _v ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState243)
    | RBRACKET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (v : (Lang.exp))), _, (vs : (Lang.exp list))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 380 "myth/parser.mly"
    ( v :: List.rev vs )
# 756 "myth/parser.ml"
         in
        _menhir_goto_ev_val_semi_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_ev_lvals_list : _menhir_env -> 'ttv_tail -> ((string * Lang.exp) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), (lvs : ((string * Lang.exp) list))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 372 "myth/parser.mly"
    ( ERcd (List.rev lvs) )
# 781 "myth/parser.ml"
         in
        _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v
    | SEMI ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | EQ ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | FUN ->
                    _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState235
                | INT _v ->
                    _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
                | LBRACE ->
                    _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState235
                | LBRACKET ->
                    _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState235
                | LID _v ->
                    _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
                | LPAREN ->
                    _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState235
                | UID _v ->
                    _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState235)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_ev_val_ios_one : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Lang.exp * Lang.exp) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState219 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (vs : ((Lang.exp * Lang.exp) list)) = _v in
        let (_menhir_stack, _menhir_s, (v1 : (Lang.exp * Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 326 "myth/parser.mly"
    ( EPFun (v1 :: List.rev vs) )
# 846 "myth/parser.ml"
         in
        _menhir_goto_ev_val_ios _menhir_env _menhir_stack _menhir_s _v
    | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (vs : ((Lang.exp * Lang.exp) list)) = _v in
        let (_menhir_stack, _menhir_s, (v : (Lang.exp * Lang.exp))) = _menhir_stack in
        let _v : ((Lang.exp * Lang.exp) list) = 
# 332 "myth/parser.mly"
    ( v :: vs )
# 857 "myth/parser.ml"
         in
        _menhir_goto_ev_val_ios_one _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_ev_val_ios : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (v : (Lang.exp)) = _v in
    let _v : (Lang.exp) = 
# 318 "myth/parser.mly"
    ( v )
# 871 "myth/parser.ml"
     in
    _menhir_goto_ev_val _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_letbind : _menhir_env -> 'ttv_tail -> (Lang.decl) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (l : (Lang.decl)) = _v in
    let (_menhir_stack, _menhir_s, (ds : (Lang.decl list))) = _menhir_stack in
    let _v : (Lang.decl list) = 
# 76 "myth/parser.mly"
    ( l::ds )
# 884 "myth/parser.ml"
     in
    _menhir_goto_decls _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_branches : _menhir_env -> 'ttv_tail -> (Lang.branch list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | PIPE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | UID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState137
            | LID _v ->
                _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _v
            | LPAREN ->
                _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState137
            | UNDERSCORE ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState137
            | ARR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, (c : (
# 21 "myth/parser.mly"
       (string)
# 919 "myth/parser.ml"
                ))) = _menhir_stack in
                let _v : (Lang.pat) = 
# 288 "myth/parser.mly"
    ( (c, None) )
# 924 "myth/parser.ml"
                 in
                _menhir_goto_pat _menhir_env _menhir_stack _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState137)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | COMMA | FATARR | FUN | IN | INT _ | LBRACE | LBRACKET | LET | LID _ | LPAREN | MATCH | PROJ _ | RBRACE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (e : (Lang.exp))), (bs : (Lang.branch list))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 223 "myth/parser.mly"
    ( EMatch (e, List.rev bs) )
# 942 "myth/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_exp_comma_list_one : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run130 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (e : (Lang.exp))), _, (es : (Lang.exp list))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 227 "myth/parser.mly"
    ( ETuple (e :: List.rev es) )
# 971 "myth/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run130 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (c : (
# 21 "myth/parser.mly"
       (string)
# 994 "myth/parser.ml"
            ))), _, (e : (Lang.exp))), _, (es : (Lang.exp list))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 219 "myth/parser.mly"
    ( ECtor (c, ETuple (e :: List.rev es)) )
# 999 "myth/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_exp_semi_list_one : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMI ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FUN ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | INT _v ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
        | LBRACE ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | LBRACKET ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | LET ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | LID _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
        | LPAREN ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | MATCH ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | PROJ _v ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
        | UID _v ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState110)
    | RBRACKET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e : (Lang.exp))), _, (es : (Lang.exp list))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 265 "myth/parser.mly"
    ( e :: List.rev es )
# 1053 "myth/parser.ml"
         in
        _menhir_goto_exp_semi_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_exp_lexps_list : _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * Lang.exp) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | DOT ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, (es : ((string * Lang.exp) list))) = _menhir_stack in
                let _v : (Lang.exp) = 
# 243 "myth/parser.mly"
    ( ERcd (List.rev es) )
# 1083 "myth/parser.ml"
                 in
                _menhir_goto_record_proj_exp _menhir_env _menhir_stack _menhir_s _v
            | COMMA | FATARR | FUN | IN | INT _ | LBRACE | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | PROJ _ | RBRACE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, (es : ((string * Lang.exp) list))) = _menhir_stack in
                let _v : (Lang.exp) = 
# 231 "myth/parser.mly"
    ( ERcd (List.rev es) )
# 1092 "myth/parser.ml"
                 in
                _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | SEMI ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState170 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (c : (
# 21 "myth/parser.mly"
       (string)
# 1121 "myth/parser.ml"
            ))), _, (es : ((string * Lang.exp) list))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 221 "myth/parser.mly"
    ( ECtor (c, ERcd (List.rev es)) )
# 1126 "myth/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | SEMI ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_ev_val : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, (l : (
# 20 "myth/parser.mly"
       (string)
# 1150 "myth/parser.ml"
        ))), _, (v : (Lang.exp))) = _menhir_stack in
        let _v : ((string * Lang.exp) list) = 
# 396 "myth/parser.mly"
    ( [(l,v)] )
# 1155 "myth/parser.ml"
         in
        _menhir_goto_ev_lvals_list _menhir_env _menhir_stack _v
    | MenhirState235 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, (vs : ((string * Lang.exp) list))), (l : (
# 20 "myth/parser.mly"
       (string)
# 1164 "myth/parser.ml"
        ))), _, (v : (Lang.exp))) = _menhir_stack in
        let _v : ((string * Lang.exp) list) = 
# 398 "myth/parser.mly"
    ( (l,v)::vs )
# 1169 "myth/parser.ml"
         in
        _menhir_goto_ev_lvals_list _menhir_env _menhir_stack _v
    | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState241
            | INT _v ->
                _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
            | LBRACE ->
                _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState241
            | LBRACKET ->
                _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState241
            | LID _v ->
                _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
            | LPAREN ->
                _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState241
            | UID _v ->
                _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState241)
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (v : (Lang.exp))) = _menhir_stack in
            let _v : (Lang.exp list) = 
# 378 "myth/parser.mly"
    ( [v] )
# 1206 "myth/parser.ml"
             in
            _menhir_goto_ev_val_semi_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState243 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (vs : (Lang.exp list))), _, (v : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 386 "myth/parser.mly"
    ( v::vs )
# 1222 "myth/parser.ml"
         in
        _menhir_goto_ev_val_semi_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState241 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (v : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 384 "myth/parser.mly"
    ( [v] )
# 1232 "myth/parser.ml"
         in
        _menhir_goto_ev_val_semi_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState205 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState248
            | INT _v ->
                _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState248 _v
            | LBRACE ->
                _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState248
            | LBRACKET ->
                _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState248
            | LID _v ->
                _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState248 _v
            | LPAREN ->
                _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState248
            | UID _v ->
                _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState248 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState248)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (v : (Lang.exp))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 366 "myth/parser.mly"
    ( v )
# 1271 "myth/parser.ml"
             in
            _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState251 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (vs : (Lang.exp list))), _, (v : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 392 "myth/parser.mly"
    ( v::vs )
# 1287 "myth/parser.ml"
         in
        _menhir_goto_ev_val_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState256 | MenhirState248 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (v : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 390 "myth/parser.mly"
    ( [v] )
# 1297 "myth/parser.ml"
         in
        _menhir_goto_ev_val_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState203 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState256
            | INT _v ->
                _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState256 _v
            | LBRACE ->
                _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState256
            | LBRACKET ->
                _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState256
            | LID _v ->
                _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState256 _v
            | LPAREN ->
                _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState256
            | UID _v ->
                _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState256 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState256)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (c : (
# 21 "myth/parser.mly"
       (string)
# 1335 "myth/parser.ml"
            ))), _, (v : (Lang.exp))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 350 "myth/parser.mly"
    ( ECtor (c, v) )
# 1340 "myth/parser.ml"
             in
            _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState200 | MenhirState265 | MenhirState267 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (v : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 314 "myth/parser.mly"
    ( v )
# 1356 "myth/parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState200 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | SEMI ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | FUN ->
                    _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState265
                | INT _v ->
                    _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState265 _v
                | LBRACE ->
                    _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState265
                | LBRACKET ->
                    _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState265
                | LID _v ->
                    _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState265 _v
                | LPAREN ->
                    _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState265
                | UID _v ->
                    _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState265 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState265)
            | RBRACE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (v : (Lang.exp))) = _menhir_stack in
                let _v : (Lang.exp list) = 
# 404 "myth/parser.mly"
    ( [v] )
# 1394 "myth/parser.ml"
                 in
                _menhir_goto_evidencelist _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState267 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (vs : (Lang.exp list))), _, (v : (Lang.exp))) = _menhir_stack in
            let _v : (Lang.exp list) = 
# 412 "myth/parser.mly"
    ( v::vs )
# 1410 "myth/parser.ml"
             in
            _menhir_goto_evidencelist_one _menhir_env _menhir_stack _menhir_s _v
        | MenhirState265 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (v : (Lang.exp))) = _menhir_stack in
            let _v : (Lang.exp list) = 
# 410 "myth/parser.mly"
    ( [v] )
# 1420 "myth/parser.ml"
             in
            _menhir_goto_evidencelist_one _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            _menhir_fail ())
    | _ ->
        _menhir_fail ()

and _menhir_goto_ev_val_io_one : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState225 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (v2 : (Lang.exp)) = _v in
        let (_menhir_stack, _menhir_s, (v1 : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp * Lang.exp) = 
# 336 "myth/parser.mly"
    ( (v1, v2) )
# 1439 "myth/parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState200 | MenhirState265 | MenhirState267 | MenhirState256 | MenhirState203 | MenhirState248 | MenhirState251 | MenhirState205 | MenhirState241 | MenhirState243 | MenhirState208 | MenhirState235 | MenhirState211 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | PIPE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | FUN ->
                    _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState219
                | INT _v ->
                    _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
                | LBRACE ->
                    _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState219
                | LBRACKET ->
                    _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState219
                | LID _v ->
                    _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
                | LPAREN ->
                    _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState219
                | UID _v ->
                    _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState219)
            | COMMA | RBRACE | RBRACKET | RPAREN | SEMI ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (v : (Lang.exp * Lang.exp))) = _menhir_stack in
                let _v : (Lang.exp) = 
# 324 "myth/parser.mly"
    ( EPFun [v] )
# 1477 "myth/parser.ml"
                 in
                _menhir_goto_ev_val_ios _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState222 | MenhirState219 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | PIPE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | FUN ->
                    _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState222
                | INT _v ->
                    _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _v
                | LBRACE ->
                    _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState222
                | LBRACKET ->
                    _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState222
                | LID _v ->
                    _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _v
                | LPAREN ->
                    _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState222
                | UID _v ->
                    _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState222)
            | COMMA | RBRACE | RBRACKET | RPAREN | SEMI ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (v : (Lang.exp * Lang.exp))) = _menhir_stack in
                let _v : ((Lang.exp * Lang.exp) list) = 
# 330 "myth/parser.mly"
    ( [v] )
# 1520 "myth/parser.ml"
                 in
                _menhir_goto_ev_val_ios_one _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            _menhir_fail ())
    | MenhirState228 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (v2 : (Lang.exp)) = _v in
        let (_menhir_stack, _menhir_s, (v1 : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 342 "myth/parser.mly"
    ( EPFun [(v1, v2)] )
# 1539 "myth/parser.ml"
         in
        _menhir_goto_ev_val_io_one _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run225 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.exp) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FUN ->
        _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | INT _v ->
        _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
    | LBRACE ->
        _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | LBRACKET ->
        _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | LID _v ->
        _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
    | LPAREN ->
        _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState225
    | UID _v ->
        _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState225

and _menhir_goto_exp_app_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FUN ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | INT _v ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
    | LBRACE ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | LBRACKET ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | LET ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | LID _v ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
    | LPAREN ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | MATCH ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | PROJ _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
    | UID _v ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
    | COMMA | FATARR | IN | PIPE | RBRACE | RBRACKET | RPAREN | SEMI | WITH ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e : (Lang.exp))), _, (es : (Lang.exp list))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 177 "myth/parser.mly"
    ( appify e (List.rev es) )
# 1602 "myth/parser.ml"
         in
        _menhir_goto_exp_app _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState94

and _menhir_goto_exp_app : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (e : (Lang.exp)) = _v in
    let _v : (Lang.exp) = 
# 173 "myth/parser.mly"
    ( e )
# 1618 "myth/parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (x : (Lang.arg))), _, (e : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 201 "myth/parser.mly"
    ( EFun (x, e) )
# 1629 "myth/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (l : (
# 20 "myth/parser.mly"
       (string)
# 1638 "myth/parser.ml"
        ))), _, (e : (Lang.exp))) = _menhir_stack in
        let _v : ((string * Lang.exp) list) = 
# 255 "myth/parser.mly"
    ( [(l,e)] )
# 1643 "myth/parser.ml"
         in
        _menhir_goto_exp_lexps_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState102 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, (lexps : ((string * Lang.exp) list))), (l : (
# 20 "myth/parser.mly"
       (string)
# 1652 "myth/parser.ml"
        ))), _, (e : (Lang.exp))) = _menhir_stack in
        let _v : ((string * Lang.exp) list) = 
# 257 "myth/parser.mly"
    ( (l,e) :: lexps )
# 1657 "myth/parser.ml"
         in
        _menhir_goto_exp_lexps_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState108
            | INT _v ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
            | LBRACE ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState108
            | LBRACKET ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState108
            | LET ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState108
            | LID _v ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
            | LPAREN ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState108
            | MATCH ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState108
            | PROJ _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
            | UID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState108)
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Lang.exp))) = _menhir_stack in
            let _v : (Lang.exp list) = 
# 263 "myth/parser.mly"
    ( [e] )
# 1700 "myth/parser.ml"
             in
            _menhir_goto_exp_semi_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState110 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (es : (Lang.exp list))), _, (e : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 271 "myth/parser.mly"
    ( e :: es )
# 1716 "myth/parser.ml"
         in
        _menhir_goto_exp_semi_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState108 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (e : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 269 "myth/parser.mly"
    ( [e] )
# 1726 "myth/parser.ml"
         in
        _menhir_goto_exp_semi_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState80 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | INT _v ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
            | LBRACE ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | LBRACKET ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | LET ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | LID _v ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
            | LPAREN ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | MATCH ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | PROJ _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
            | UID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState114)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState114 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((((_menhir_stack, _menhir_s), (f : (
# 20 "myth/parser.mly"
       (string)
# 1775 "myth/parser.ml"
        ))), _, (xs : (Lang.arg list))), _), _, (t : (Lang.typ))), _, (e1 : (Lang.exp))), _, (e2 : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 205 "myth/parser.mly"
    ( ELet (f, true, List.rev xs, t, e1, e2) )
# 1780 "myth/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | MenhirState121 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState123
            | INT _v ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
            | LBRACE ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState123
            | LBRACKET ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState123
            | LET ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState123
            | LID _v ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
            | LPAREN ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState123
            | MATCH ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState123
            | PROJ _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
            | UID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState123)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState123 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((((_menhir_stack, _menhir_s), (f : (
# 20 "myth/parser.mly"
       (string)
# 1829 "myth/parser.ml"
        ))), _, (xs : (Lang.arg list))), _), _, (t : (Lang.typ))), _, (e1 : (Lang.exp))), _, (e2 : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 203 "myth/parser.mly"
    ( ELet (f, false, List.rev xs, t, e1, e2) )
# 1834 "myth/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState127
            | INT _v ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _v
            | LBRACE ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState127
            | LBRACKET ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState127
            | LET ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState127
            | LID _v ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _v
            | LPAREN ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState127
            | MATCH ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState127
            | PROJ _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _v
            | UID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState127)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | DOT ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, (e : (Lang.exp))) = _menhir_stack in
                let _v : (Lang.exp) = 
# 245 "myth/parser.mly"
    ( e )
# 1882 "myth/parser.ml"
                 in
                _menhir_goto_record_proj_exp _menhir_env _menhir_stack _menhir_s _v
            | COMMA | FATARR | FUN | IN | INT _ | LBRACE | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | PROJ _ | RBRACE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, (e : (Lang.exp))) = _menhir_stack in
                let _v : (Lang.exp) = 
# 235 "myth/parser.mly"
    ( e )
# 1891 "myth/parser.ml"
                 in
                _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (es : (Lang.exp list))), _, (e : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 251 "myth/parser.mly"
    ( e :: es )
# 1913 "myth/parser.ml"
         in
        _menhir_goto_exp_comma_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState166 | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (e : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 249 "myth/parser.mly"
    ( [e] )
# 1923 "myth/parser.ml"
         in
        _menhir_goto_exp_comma_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _v : (Lang.branch list) = 
# 276 "myth/parser.mly"
    ( [] )
# 1938 "myth/parser.ml"
             in
            _menhir_goto_branches _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState160 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, (p : (Lang.pat))), _, (e : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.branch) = 
# 282 "myth/parser.mly"
    ( (p, e) )
# 1954 "myth/parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (b : (Lang.branch)) = _v in
        let (_menhir_stack, (bs : (Lang.branch list))) = _menhir_stack in
        let _v : (Lang.branch list) = 
# 278 "myth/parser.mly"
    ( b::bs )
# 1963 "myth/parser.ml"
         in
        _menhir_goto_branches _menhir_env _menhir_stack _v
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (n : (
# 22 "myth/parser.mly"
       (int)
# 1972 "myth/parser.ml"
        ))), _, (e : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 229 "myth/parser.mly"
    ( EProj (n, e) )
# 1977 "myth/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | MenhirState67 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | INT _v ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _v
            | LBRACE ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | LBRACKET ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | LET ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | LID _v ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _v
            | LPAREN ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | MATCH ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | PROJ _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _v
            | UID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState166)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (c : (
# 21 "myth/parser.mly"
       (string)
# 2021 "myth/parser.ml"
            ))), _, (e : (Lang.exp))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 211 "myth/parser.mly"
    ( ECtor (c, e) )
# 2026 "myth/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | SEMI ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((((_menhir_stack, (x : (
# 20 "myth/parser.mly"
       (string)
# 2052 "myth/parser.ml"
                ))), _, (args : (Lang.arg list))), _), _, (t : (Lang.typ))), _, (e : (Lang.exp))) = _menhir_stack in
                let _v : (Lang.decl) = 
# 88 "myth/parser.mly"
    ( DLet (x, true, List.rev args, t, e) )
# 2057 "myth/parser.ml"
                 in
                _menhir_goto_letbind _menhir_env _menhir_stack _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | SEMI ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((((_menhir_stack, (x : (
# 20 "myth/parser.mly"
       (string)
# 2089 "myth/parser.ml"
                ))), _), _, (t : (Lang.typ))), _, (e : (Lang.exp))) = _menhir_stack in
                let _v : (Lang.decl) = 
# 84 "myth/parser.mly"
    ( DLet (x, false, [], t, e) )
# 2094 "myth/parser.ml"
                 in
                _menhir_goto_letbind _menhir_env _menhir_stack _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState186 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | SEMI ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((((_menhir_stack, (x : (
# 20 "myth/parser.mly"
       (string)
# 2126 "myth/parser.ml"
                ))), _, (args : (Lang.arg list))), _), _, (t : (Lang.typ))), _, (e : (Lang.exp))) = _menhir_stack in
                let _v : (Lang.decl) = 
# 86 "myth/parser.mly"
    ( DLet (x, false, List.rev args, t, e) )
# 2131 "myth/parser.ml"
                 in
                _menhir_goto_letbind _menhir_env _menhir_stack _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState215 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (x : (Lang.arg))), _, (e : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 348 "myth/parser.mly"
    ( EFun (x, e) )
# 2153 "myth/parser.ml"
         in
        _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_ev_val_semi_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RBRACKET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, (l : (Lang.exp list))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 364 "myth/parser.mly"
    ( list_of_exps l )
# 2174 "myth/parser.ml"
         in
        _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_ev_val_base : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState219 | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FATARR ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState228 | MenhirState225 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FATARR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | INT _v ->
                _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _v
            | LBRACE ->
                _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | LBRACKET ->
                _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | LID _v ->
                _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _v
            | LPAREN ->
                _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | UID _v ->
                _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState228)
        | COMMA | PIPE | RBRACE | RBRACKET | RPAREN | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (v : (Lang.exp))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 340 "myth/parser.mly"
    ( v )
# 2235 "myth/parser.ml"
             in
            _menhir_goto_ev_val_io_one _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState200 | MenhirState265 | MenhirState267 | MenhirState256 | MenhirState203 | MenhirState248 | MenhirState251 | MenhirState205 | MenhirState241 | MenhirState243 | MenhirState208 | MenhirState235 | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FATARR ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | RBRACE | RBRACKET | RPAREN | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (v : (Lang.exp))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 320 "myth/parser.mly"
    ( v )
# 2257 "myth/parser.ml"
             in
            _menhir_goto_ev_val _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_record_proj_exp : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (l : (
# 20 "myth/parser.mly"
       (string)
# 2288 "myth/parser.ml"
            )) = _v in
            let (_menhir_stack, _menhir_s, (e : (Lang.exp))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 233 "myth/parser.mly"
    ( ERcdProj (l,e) )
# 2294 "myth/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_exp_semi_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RBRACKET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, (l : (Lang.exp list))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 225 "myth/parser.mly"
    ( list_of_exps l )
# 2325 "myth/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run83 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 20 "myth/parser.mly"
       (string)
# 2338 "myth/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EQ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FUN ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | INT _v ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
        | LBRACE ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | LBRACKET ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | LET ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | LID _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
        | LPAREN ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | MATCH ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | PROJ _v ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
        | UID _v ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_exp_base : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState215 | MenhirState186 | MenhirState179 | MenhirState64 | MenhirState166 | MenhirState67 | MenhirState69 | MenhirState160 | MenhirState70 | MenhirState127 | MenhirState130 | MenhirState71 | MenhirState123 | MenhirState121 | MenhirState114 | MenhirState80 | MenhirState108 | MenhirState110 | MenhirState81 | MenhirState102 | MenhirState84 | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FUN ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | INT _v ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
        | LBRACE ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | LBRACKET ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | LET ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | LID _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
        | LPAREN ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | MATCH ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | PROJ _v ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
        | UID _v ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
        | COMMA | FATARR | IN | PIPE | RBRACE | RBRACKET | RPAREN | SEMI | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Lang.exp))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 179 "myth/parser.mly"
    ( e )
# 2416 "myth/parser.ml"
             in
            _menhir_goto_exp_app _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState92)
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (e : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 183 "myth/parser.mly"
    ( [e] )
# 2430 "myth/parser.ml"
         in
        _menhir_goto_exp_app_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState94 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (es : (Lang.exp list))), _, (e : (Lang.exp))) = _menhir_stack in
        let _v : (Lang.exp list) = 
# 185 "myth/parser.mly"
    ( e::es )
# 2440 "myth/parser.ml"
         in
        _menhir_goto_exp_app_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run57 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState59
            | LID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
            | LPAREN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState59
            | UNIT ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState59
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_evidencelist : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.exp list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | HOLE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((((_menhir_stack, (x : (
# 20 "myth/parser.mly"
       (string)
# 2512 "myth/parser.ml"
                ))), _), _, (t : (Lang.typ))), _, (es : (Lang.exp list))) = _menhir_stack in
                let _v : (Lang.synth_problem) = 
# 104 "myth/parser.mly"
    ( (x, t, es) )
# 2517 "myth/parser.ml"
                 in
                let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | EOF ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s, (_1 : (Lang.decl list))), (_2 : (Lang.synth_problem))) = _menhir_stack in
                    let _v : (Lang.prog) = 
# 66 "myth/parser.mly"
    ( (List.rev _1, _2) )
# 2531 "myth/parser.ml"
                     in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_1 : (Lang.prog)) = _v in
                    Obj.magic _1
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run201 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 21 "myth/parser.mly"
       (string)
# 2565 "myth/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (
# 20 "myth/parser.mly"
       (string)
# 2579 "myth/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s, (c : (
# 21 "myth/parser.mly"
       (string)
# 2584 "myth/parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 354 "myth/parser.mly"
    ( ECtor (c, EVar x) )
# 2589 "myth/parser.ml"
         in
        _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FUN ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState203
        | INT _v ->
            _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _v
        | LBRACE ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState203
        | LBRACKET ->
            _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState203
        | LID _v ->
            _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _v
        | LPAREN ->
            _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState203
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState203 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (c : (
# 21 "myth/parser.mly"
       (string)
# 2617 "myth/parser.ml"
            ))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 356 "myth/parser.mly"
    ( ECtor (c, EUnit) )
# 2622 "myth/parser.ml"
             in
            _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v
        | UID _v ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState203)
    | UID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (c2 : (
# 21 "myth/parser.mly"
       (string)
# 2638 "myth/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s, (c1 : (
# 21 "myth/parser.mly"
       (string)
# 2643 "myth/parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 352 "myth/parser.mly"
    ( ECtor (c1, ECtor (c2, EUnit)) )
# 2648 "myth/parser.ml"
         in
        _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v
    | COMMA | FATARR | PIPE | RBRACE | RBRACKET | RPAREN | SEMI ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (c : (
# 21 "myth/parser.mly"
       (string)
# 2656 "myth/parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 362 "myth/parser.mly"
    ( ECtor (c, EUnit) )
# 2661 "myth/parser.ml"
         in
        _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run205 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FUN ->
        _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | INT _v ->
        _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
    | LBRACE ->
        _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | LBRACKET ->
        _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | LID _v ->
        _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
    | LPAREN ->
        _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState205
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState205 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (Lang.exp) = 
# 368 "myth/parser.mly"
    ( EUnit )
# 2698 "myth/parser.ml"
         in
        _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v
    | UID _v ->
        _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState205

and _menhir_run207 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 20 "myth/parser.mly"
       (string)
# 2711 "myth/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (x : (
# 20 "myth/parser.mly"
       (string)
# 2719 "myth/parser.ml"
    )) = _v in
    let _v : (Lang.exp) = 
# 346 "myth/parser.mly"
    ( EVar x )
# 2724 "myth/parser.ml"
     in
    _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run208 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FUN ->
        _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState208
    | INT _v ->
        _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v
    | LBRACE ->
        _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState208
    | LBRACKET ->
        _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState208
    | LID _v ->
        _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v
    | LPAREN ->
        _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState208
    | UID _v ->
        _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v
    | RBRACKET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState208 in
        let _v : (Lang.exp list) = 
# 376 "myth/parser.mly"
    ( [] )
# 2754 "myth/parser.ml"
         in
        _menhir_goto_ev_val_semi_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState208

and _menhir_run209 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState211
            | INT _v ->
                _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState211 _v
            | LBRACE ->
                _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState211
            | LBRACKET ->
                _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState211
            | LID _v ->
                _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState211 _v
            | LPAREN ->
                _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState211
            | UID _v ->
                _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState211 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState211)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run212 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 24 "myth/parser.mly"
       (int)
# 2812 "myth/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (c : (
# 24 "myth/parser.mly"
       (int)
# 2820 "myth/parser.ml"
    )) = _v in
    let _v : (Lang.exp) = 
# 360 "myth/parser.mly"
    ( ctor_of_int c )
# 2825 "myth/parser.ml"
     in
    _menhir_goto_ev_val_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run213 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState213
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState213

and _menhir_run179 : _menhir_env -> ((('ttv_tail) * (
# 20 "myth/parser.mly"
       (string)
# 2845 "myth/parser.ml"
)) * _menhir_state) * _menhir_state * (Lang.typ) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FUN ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | INT _v ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | LBRACE ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LBRACKET ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LET ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | LID _v ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | LPAREN ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | MATCH ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState179
    | PROJ _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | UID _v ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState179

and _menhir_run65 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 21 "myth/parser.mly"
       (string)
# 2879 "myth/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState170)
    | LID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (
# 20 "myth/parser.mly"
       (string)
# 2904 "myth/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s, (c : (
# 21 "myth/parser.mly"
       (string)
# 2909 "myth/parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 215 "myth/parser.mly"
    ( ECtor (c, EVar x) )
# 2914 "myth/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FUN ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | INT _v ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
        | LBRACE ->
            _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | LBRACKET ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | LET ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | LID _v ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
        | LPAREN ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | MATCH ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | PROJ _v ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState67 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (c : (
# 21 "myth/parser.mly"
       (string)
# 2948 "myth/parser.ml"
            ))) = _menhir_stack in
            let _v : (Lang.exp) = 
# 217 "myth/parser.mly"
    ( ECtor (c, EUnit) )
# 2953 "myth/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | UID _v ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState67)
    | UID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (c2 : (
# 21 "myth/parser.mly"
       (string)
# 2969 "myth/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s, (c1 : (
# 21 "myth/parser.mly"
       (string)
# 2974 "myth/parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 213 "myth/parser.mly"
    ( ECtor (c1, ECtor (c2, EUnit)) )
# 2979 "myth/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | COMMA | FATARR | FUN | IN | INT _ | LBRACKET | LET | MATCH | PIPE | PROJ _ | RBRACE | RBRACKET | RPAREN | SEMI | WITH ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (c : (
# 21 "myth/parser.mly"
       (string)
# 2987 "myth/parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 209 "myth/parser.mly"
    ( ECtor (c, EUnit) )
# 2992 "myth/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run69 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 22 "myth/parser.mly"
       (int)
# 3005 "myth/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FUN ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | INT _v ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
    | LBRACE ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | LBRACKET ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | LET ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | LID _v ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
    | LPAREN ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | MATCH ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | PROJ _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
    | UID _v ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState69

and _menhir_run70 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FUN ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | INT _v ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
    | LBRACE ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | LBRACKET ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | LET ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | LID _v ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
    | LPAREN ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | MATCH ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | PROJ _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
    | UID _v ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState70

and _menhir_run71 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FUN ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | INT _v ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
    | LBRACE ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | LBRACKET ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | LET ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | LID _v ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
    | LPAREN ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | MATCH ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | PROJ _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState71 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (Lang.exp) = 
# 237 "myth/parser.mly"
    ( EUnit )
# 3101 "myth/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | UID _v ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71

and _menhir_run73 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 20 "myth/parser.mly"
       (string)
# 3114 "myth/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : (
# 20 "myth/parser.mly"
       (string)
# 3126 "myth/parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 241 "myth/parser.mly"
    ( EVar x )
# 3131 "myth/parser.ml"
         in
        _menhir_goto_record_proj_exp _menhir_env _menhir_stack _menhir_s _v
    | COMMA | FATARR | FUN | IN | INT _ | LBRACE | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | PROJ _ | RBRACE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : (
# 20 "myth/parser.mly"
       (string)
# 3139 "myth/parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.exp) = 
# 199 "myth/parser.mly"
    ( EVar x )
# 3144 "myth/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run74 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        _menhir_reduce3 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | REC ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            _menhir_reduce3 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run81 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FUN ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | INT _v ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
    | LBRACE ->
        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | LBRACKET ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | LET ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | LID _v ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
    | LPAREN ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | MATCH ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | PROJ _v ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
    | UID _v ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
    | RBRACKET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState81 in
        let _v : (Lang.exp list) = 
# 261 "myth/parser.mly"
    ( [] )
# 3220 "myth/parser.ml"
         in
        _menhir_goto_exp_semi_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState81

and _menhir_run82 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82

and _menhir_run85 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 24 "myth/parser.mly"
       (int)
# 3244 "myth/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (c : (
# 24 "myth/parser.mly"
       (int)
# 3252 "myth/parser.ml"
    )) = _v in
    let _v : (Lang.exp) = 
# 207 "myth/parser.mly"
    ( ctor_of_int c )
# 3257 "myth/parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run86 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState86
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState86

and _menhir_goto_ctor : _menhir_env -> 'ttv_tail -> (Lang.ctor) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (c : (Lang.ctor)) = _v in
    let (_menhir_stack, (cs : (Lang.ctor list))) = _menhir_stack in
    let _v : (Lang.ctor list) = 
# 94 "myth/parser.mly"
    ( c::cs )
# 3283 "myth/parser.ml"
     in
    _menhir_goto_ctors _menhir_env _menhir_stack _v

and _menhir_goto_typ_rcd_list : _menhir_env -> 'ttv_tail -> ((string * Lang.typ) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), (ts : ((string * Lang.typ) list))) = _menhir_stack in
        let _v : (Lang.typ) = 
# 120 "myth/parser.mly"
      ( TRcd (List.rev ts) )
# 3302 "myth/parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState19 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (ts : (Lang.typ list))), _, (t : (Lang.typ))) = _menhir_stack in
            let _v : (Lang.typ list) = 
# 156 "myth/parser.mly"
                                           ( t :: ts )
# 3313 "myth/parser.ml"
             in
            _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
        | MenhirState38 | MenhirState33 | MenhirState30 | MenhirState16 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
            let _v : (Lang.typ list) = 
# 152 "myth/parser.mly"
                ( [t] )
# 3323 "myth/parser.ml"
             in
            _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
        | MenhirState197 | MenhirState184 | MenhirState177 | MenhirState119 | MenhirState78 | MenhirState62 | MenhirState59 | MenhirState8 | MenhirState10 | MenhirState46 | MenhirState36 | MenhirState14 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | STAR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LBRACE ->
                    _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState30
                | LID _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState30 _v
                | LPAREN ->
                    _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState30
                | UNIT ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState30
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState30)
            | ARR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
                let _v : (Lang.typ) = 
# 133 "myth/parser.mly"
                ( t )
# 3354 "myth/parser.ml"
                 in
                _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v
            | EQ | IMPLIES | LET | PIPE | RBRACE | RPAREN | SEMI | TYPE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
                let _v : (Lang.typ) = 
# 116 "myth/parser.mly"
                ( t )
# 3363 "myth/parser.ml"
                 in
                _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            _menhir_fail ())
    | SEMI ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LBRACE ->
                    _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState46
                | LID _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
                | LPAREN ->
                    _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState46
                | UNIT ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState46
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_typ_tuple_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.typ list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (ts : (Lang.typ list)) = _v in
    let _v : (Lang.typ) = 
# 139 "myth/parser.mly"
                      ( TTuple (ts) )
# 3427 "myth/parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
        let _v : (Lang.typ) = 
# 132 "myth/parser.mly"
                ( t )
# 3440 "myth/parser.ml"
         in
        _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v
    | EQ | IMPLIES | LET | PIPE | RBRACE | RPAREN | SEMI | TYPE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
        let _v : (Lang.typ) = 
# 112 "myth/parser.mly"
                ( t )
# 3449 "myth/parser.ml"
         in
        _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run19 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.typ list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | LID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _v
    | LPAREN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | UNIT ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState19

and _menhir_goto_ctors : _menhir_env -> 'ttv_tail -> (Lang.ctor list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | PIPE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | UID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | OF ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LBRACE ->
                    _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState8
                | LID _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v
                | LPAREN ->
                    _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState8
                | UNIT ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState8
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState8)
            | LET | PIPE | TYPE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, (c : (
# 21 "myth/parser.mly"
       (string)
# 3517 "myth/parser.ml"
                ))) = _menhir_stack in
                let _v : (Lang.ctor) = 
# 100 "myth/parser.mly"
    ( (c, TUnit) )
# 3522 "myth/parser.ml"
                 in
                _menhir_goto_ctor _menhir_env _menhir_stack _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | LET | TYPE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, (d : (
# 20 "myth/parser.mly"
       (string)
# 3540 "myth/parser.ml"
        ))), (cs : (Lang.ctor list))) = _menhir_stack in
        let _v : (Lang.decl) = 
# 80 "myth/parser.mly"
    ( DData (d, List.rev cs) )
# 3545 "myth/parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (d : (Lang.decl)) = _v in
        let (_menhir_stack, _menhir_s, (ds : (Lang.decl list))) = _menhir_stack in
        let _v : (Lang.decl list) = 
# 74 "myth/parser.mly"
    ( d::ds )
# 3554 "myth/parser.ml"
         in
        _menhir_goto_decls _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_goto_arg_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.arg list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState56 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState62
            | LID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
            | LPAREN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState62
            | UNIT ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState62
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62)
        | LPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState56)
    | MenhirState76 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState77 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState78
            | LID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
            | LPAREN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState78
            | UNIT ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState78
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78)
        | LPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77)
    | MenhirState117 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState118 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | LID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState119 _v
            | LPAREN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | UNIT ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState119)
        | LPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState118
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState118)
    | MenhirState196 | MenhirState176 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState183 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState184
            | LID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState184 _v
            | LPAREN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState184
            | UNIT ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState184
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState184)
        | LPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState183
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState183)
    | _ ->
        _menhir_fail ()

and _menhir_goto_typ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.typ) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (t : (Lang.typ))), _, (t2 : (Lang.typ))) = _menhir_stack in
        let _v : (Lang.typ) = 
# 129 "myth/parser.mly"
                               ( TArr (t, t2) )
# 3701 "myth/parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (t : (Lang.typ)) = _v in
        let _v : (Lang.typ) = 
# 111 "myth/parser.mly"
                ( t )
# 3709 "myth/parser.ml"
         in
        _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, (l : (
# 20 "myth/parser.mly"
       (string)
# 3718 "myth/parser.ml"
        ))), _, (t : (Lang.typ))) = _menhir_stack in
        let _v : ((string * Lang.typ) list) = 
# 124 "myth/parser.mly"
      ( [(l,t)] )
# 3723 "myth/parser.ml"
         in
        _menhir_goto_typ_rcd_list _menhir_env _menhir_stack _v
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, (ts : ((string * Lang.typ) list))), (l : (
# 20 "myth/parser.mly"
       (string)
# 3732 "myth/parser.ml"
        ))), _, (t : (Lang.typ))) = _menhir_stack in
        let _v : ((string * Lang.typ) list) = 
# 126 "myth/parser.mly"
      ( (l,t)::ts )
# 3737 "myth/parser.ml"
         in
        _menhir_goto_typ_rcd_list _menhir_env _menhir_stack _v
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (t : (Lang.typ))) = _menhir_stack in
            let _v : (Lang.typ) = 
# 162 "myth/parser.mly"
                        ( t )
# 3753 "myth/parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            (match _menhir_s with
            | MenhirState19 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, (ts : (Lang.typ list))), _, (t : (Lang.typ))) = _menhir_stack in
                let _v : (Lang.typ list) = 
# 154 "myth/parser.mly"
                                           ( t :: ts )
# 3764 "myth/parser.ml"
                 in
                _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
            | MenhirState38 | MenhirState33 | MenhirState30 | MenhirState16 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
                let _v : (Lang.typ list) = 
# 150 "myth/parser.mly"
                ( [t] )
# 3774 "myth/parser.ml"
                 in
                _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
            | MenhirState197 | MenhirState184 | MenhirState177 | MenhirState119 | MenhirState78 | MenhirState62 | MenhirState59 | MenhirState8 | MenhirState10 | MenhirState46 | MenhirState36 | MenhirState14 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | STAR ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | LBRACE ->
                        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState33
                    | LID _v ->
                        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
                    | LPAREN ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState33
                    | UNIT ->
                        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState33
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33)
                | ARR ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
                    let _v : (Lang.typ) = 
# 135 "myth/parser.mly"
                ( t )
# 3805 "myth/parser.ml"
                     in
                    _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v
                | EQ | IMPLIES | LET | PIPE | RBRACE | RPAREN | SEMI | TYPE ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
                    let _v : (Lang.typ) = 
# 114 "myth/parser.mly"
                ( t )
# 3814 "myth/parser.ml"
                     in
                    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, (c : (
# 21 "myth/parser.mly"
       (string)
# 3837 "myth/parser.ml"
        ))), _, (t : (Lang.typ))) = _menhir_stack in
        let _v : (Lang.ctor) = 
# 98 "myth/parser.mly"
    ( (c, t)  )
# 3842 "myth/parser.ml"
         in
        _menhir_goto_ctor _menhir_env _menhir_stack _v
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (x : (
# 20 "myth/parser.mly"
       (string)
# 3857 "myth/parser.ml"
            ))), _, (t : (Lang.typ))) = _menhir_stack in
            let _v : (Lang.arg) = 
# 189 "myth/parser.mly"
    ( (x, t) )
# 3862 "myth/parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            (match _menhir_s with
            | MenhirState86 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ARR ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | FUN ->
                        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                    | INT _v ->
                        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
                    | LBRACE ->
                        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                    | LBRACKET ->
                        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                    | LET ->
                        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                    | LID _v ->
                        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
                    | LPAREN ->
                        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                    | MATCH ->
                        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                    | PROJ _v ->
                        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
                    | UID _v ->
                        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState88)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | MenhirState183 | MenhirState56 | MenhirState118 | MenhirState77 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, (xs : (Lang.arg list))), _, (x : (Lang.arg))) = _menhir_stack in
                let _v : (Lang.arg list) = 
# 195 "myth/parser.mly"
    ( x :: xs )
# 3913 "myth/parser.ml"
                 in
                _menhir_goto_arg_list _menhir_env _menhir_stack _menhir_s _v
            | MenhirState213 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ARR ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | FUN ->
                        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState215
                    | INT _v ->
                        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
                    | LBRACE ->
                        _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState215
                    | LBRACKET ->
                        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState215
                    | LET ->
                        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState215
                    | LID _v ->
                        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
                    | LPAREN ->
                        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState215
                    | MATCH ->
                        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState215
                    | PROJ _v ->
                        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
                    | UID _v ->
                        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState215)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState64
            | INT _v ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _v
            | LBRACE ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState64
            | LBRACKET ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState64
            | LET ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState64
            | LID _v ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _v
            | LPAREN ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState64
            | MATCH ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState64
            | PROJ _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _v
            | UID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState64)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | INT _v ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
            | LBRACE ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | LBRACKET ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | LET ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | LID _v ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
            | LPAREN ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | MATCH ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | PROJ _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
            | UID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState119 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | INT _v ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
            | LBRACE ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | LBRACKET ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | LET ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | LID _v ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
            | LPAREN ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | MATCH ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | PROJ _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
            | UID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState121)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState177 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState184 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FUN ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | INT _v ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState186 _v
            | LBRACE ->
                _menhir_run82 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | LBRACKET ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | LET ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | LID _v ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState186 _v
            | LPAREN ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | MATCH ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | PROJ _v ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState186 _v
            | UID _v ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState186 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState186)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState197 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | IMPLIES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | FUN ->
                    _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState200
                | INT _v ->
                    _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _v
                | LBRACE ->
                    _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState200
                | LBRACKET ->
                    _menhir_run208 _menhir_env (Obj.magic _menhir_stack) MenhirState200
                | LID _v ->
                    _menhir_run207 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _v
                | LPAREN ->
                    _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState200
                | UID _v ->
                    _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _v
                | RBRACE ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_s = MenhirState200 in
                    let _v : (Lang.exp list) = 
# 402 "myth/parser.mly"
    ( [] )
# 4174 "myth/parser.ml"
                     in
                    _menhir_goto_evidencelist _menhir_env _menhir_stack _menhir_s _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState200)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_typ_non_arrow : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.typ) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | LID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v
        | LPAREN ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | UNIT ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_typ_tuple_list_one : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.typ list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | ARR | EQ | IMPLIES | LET | PIPE | RBRACE | RPAREN | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (t : (Lang.typ))), _, (ts : (Lang.typ list))) = _menhir_stack in
            let _v : (Lang.typ list) = 
# 145 "myth/parser.mly"
                                           ( t :: List.rev ts )
# 4244 "myth/parser.ml"
             in
            _menhir_goto_typ_tuple_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | ARR | EQ | IMPLIES | LET | PIPE | RBRACE | RPAREN | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (t : (Lang.typ))), _, (ts : (Lang.typ list))) = _menhir_stack in
            let _v : (Lang.typ list) = 
# 146 "myth/parser.mly"
                                           ( t :: List.rev ts )
# 4266 "myth/parser.ml"
             in
            _menhir_goto_typ_tuple_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | ARR | EQ | IMPLIES | LET | PIPE | RBRACE | RPAREN | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (t : (Lang.typ))), _, (ts : (Lang.typ list))) = _menhir_stack in
            let _v : (Lang.typ list) = 
# 144 "myth/parser.mly"
                                           ( t :: List.rev ts )
# 4288 "myth/parser.ml"
             in
            _menhir_goto_typ_tuple_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
        | ARR | EQ | IMPLIES | LET | PIPE | RBRACE | RPAREN | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (t : (Lang.typ))), _, (ts : (Lang.typ list))) = _menhir_stack in
            let _v : (Lang.typ list) = 
# 143 "myth/parser.mly"
                                           ( t :: List.rev ts )
# 4310 "myth/parser.ml"
             in
            _menhir_goto_typ_tuple_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_run2 : _menhir_env -> 'ttv_tail -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _v : (Lang.ctor list) = 
# 92 "myth/parser.mly"
    ( [] )
# 4345 "myth/parser.ml"
             in
            _menhir_goto_ctors _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run54 : _menhir_env -> 'ttv_tail -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        _menhir_reduce3 _menhir_env (Obj.magic _menhir_stack) MenhirState55
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_reduce3 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Lang.arg list) = 
# 193 "myth/parser.mly"
    ( [] )
# 4380 "myth/parser.ml"
     in
    _menhir_goto_arg_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState267 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState265 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState256 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState251 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState248 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState243 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState241 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState235 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState228 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState225 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState219 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState215 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState213 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState205 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState203 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState200 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState197 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState196 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState192 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState186 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState184 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState177 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState176 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState170 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState160 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState155 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState152 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState148 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState137 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState123 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState121 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState119 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState117 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState114 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState110 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState108 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState102 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState94 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState86 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState80 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState76 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState67 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState56 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (Lang.typ) = 
# 165 "myth/parser.mly"
         ( TUnit )
# 4697 "myth/parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState197 | MenhirState184 | MenhirState177 | MenhirState119 | MenhirState78 | MenhirState62 | MenhirState59 | MenhirState8 | MenhirState10 | MenhirState46 | MenhirState36 | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState16
            | LID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
            | LPAREN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState16
            | UNIT ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState16
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16)
        | ARR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
            let _v : (Lang.typ) = 
# 136 "myth/parser.mly"
                ( t )
# 4729 "myth/parser.ml"
             in
            _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v
        | EQ | IMPLIES | LET | PIPE | RBRACE | RPAREN | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
            let _v : (Lang.typ) = 
# 115 "myth/parser.mly"
                ( t )
# 4738 "myth/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState38 | MenhirState33 | MenhirState30 | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
        let _v : (Lang.typ list) = 
# 151 "myth/parser.mly"
                ( [t] )
# 4754 "myth/parser.ml"
         in
        _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (ts : (Lang.typ list))), _, (t : (Lang.typ))) = _menhir_stack in
        let _v : (Lang.typ list) = 
# 155 "myth/parser.mly"
                                           ( t :: ts )
# 4764 "myth/parser.ml"
         in
        _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState10
    | LID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState10 _v
    | LPAREN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState10
    | UNIT ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState10
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState10

and _menhir_run11 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 20 "myth/parser.mly"
       (string)
# 4792 "myth/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (d : (
# 20 "myth/parser.mly"
       (string)
# 4800 "myth/parser.ml"
    )) = _v in
    let _v : (Lang.typ) = 
# 159 "myth/parser.mly"
          ( TBase d )
# 4805 "myth/parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (ts : (Lang.typ list))), _, (t : (Lang.typ))) = _menhir_stack in
        let _v : (Lang.typ list) = 
# 153 "myth/parser.mly"
                                           ( t :: ts )
# 4816 "myth/parser.ml"
         in
        _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState38 | MenhirState33 | MenhirState30 | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
        let _v : (Lang.typ list) = 
# 149 "myth/parser.mly"
                ( [t] )
# 4826 "myth/parser.ml"
         in
        _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState197 | MenhirState184 | MenhirState177 | MenhirState119 | MenhirState78 | MenhirState62 | MenhirState59 | MenhirState8 | MenhirState10 | MenhirState46 | MenhirState14 | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState38
            | LID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
            | LPAREN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState38
            | UNIT ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState38
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38)
        | ARR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
            let _v : (Lang.typ) = 
# 134 "myth/parser.mly"
                ( t )
# 4857 "myth/parser.ml"
             in
            _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v
        | EQ | IMPLIES | LET | PIPE | RBRACE | RPAREN | SEMI | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Lang.typ))) = _menhir_stack in
            let _v : (Lang.typ) = 
# 113 "myth/parser.mly"
                ( t )
# 4866 "myth/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run12 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState14
            | LID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState14 _v
            | LPAREN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState14
            | UNIT ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState14
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_decls : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.decl list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LID _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | COLON ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_s = MenhirState176 in
                    let _menhir_stack = (_menhir_stack, _menhir_s) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | LBRACE ->
                        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState177
                    | LID _v ->
                        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _v
                    | LPAREN ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState177
                    | UNIT ->
                        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState177
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState177)
                | LPAREN ->
                    _menhir_reduce3 _menhir_env (Obj.magic _menhir_stack) MenhirState176
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState176)
            | REC ->
                _menhir_run54 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | TYPE ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState192 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LID _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | COLON ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_s = MenhirState196 in
                    let _menhir_stack = (_menhir_stack, _menhir_s) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | LBRACE ->
                        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState197
                    | LID _v ->
                        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v
                    | LPAREN ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState197
                    | UNIT ->
                        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState197
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState197)
                | LPAREN ->
                    _menhir_reduce3 _menhir_env (Obj.magic _menhir_stack) MenhirState196
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState196)
            | REC ->
                _menhir_run54 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | TYPE ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce13 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Lang.decl list) = 
# 72 "myth/parser.mly"
    ( [] )
# 5043 "myth/parser.ml"
     in
    _menhir_goto_decls _menhir_env _menhir_stack _menhir_s _v

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and decls : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Lang.decl list) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce13 _menhir_env (Obj.magic _menhir_stack) MenhirState0)

and prog : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Lang.prog) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce13 _menhir_env (Obj.magic _menhir_stack) MenhirState192)

# 269 "<standard.mly>"
  

# 5086 "myth/parser.ml"
