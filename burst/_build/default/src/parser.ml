
module MenhirBasics = struct
  
  exception Error
  
  let _eRR : exn =
    Error
  
  type token = 
    | WITH
    | WILDCARD
    | VAL
    | UNIT
    | UID of (
# 22 "src/parser.mly"
       (string)
# 18 "src/parser.ml"
  )
    | TYPE
    | SYNTH
    | STR of (
# 23 "src/parser.mly"
       (string)
# 25 "src/parser.ml"
  )
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
    | LID of (
# 21 "src/parser.mly"
       (string)
# 42 "src/parser.ml"
  )
    | LET
    | LBRACKET
    | INT of (
# 26 "src/parser.mly"
       (int)
# 49 "src/parser.ml"
  )
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
  
end

include MenhirBasics

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState160
  | MenhirState157
  | MenhirState150
  | MenhirState147
  | MenhirState143
  | MenhirState142
  | MenhirState141
  | MenhirState139
  | MenhirState136
  | MenhirState134
  | MenhirState129
  | MenhirState125
  | MenhirState122
  | MenhirState117
  | MenhirState115
  | MenhirState110
  | MenhirState105
  | MenhirState100
  | MenhirState97
  | MenhirState93
  | MenhirState92
  | MenhirState90
  | MenhirState84
  | MenhirState81
  | MenhirState77
  | MenhirState76
  | MenhirState75
  | MenhirState74
  | MenhirState73
  | MenhirState70
  | MenhirState69
  | MenhirState68
  | MenhirState67
  | MenhirState66
  | MenhirState65
  | MenhirState63
  | MenhirState62
  | MenhirState45
  | MenhirState42
  | MenhirState39
  | MenhirState36
  | MenhirState28
  | MenhirState25
  | MenhirState21
  | MenhirState20
  | MenhirState17
  | MenhirState13
  | MenhirState10
  | MenhirState6
  | MenhirState5
  | MenhirState3
  | MenhirState0

# 1 "src/parser.mly"
  
open MyStdLib
open Lang

let rec appify (e:Expr.t) (es:Expr.t list) : Expr.t =
  match es with
  | [] -> e
  | e'::es -> appify (Expr.mk_app e e') es

let mk_unctor_or_ctor_by_name
      (c:String.t)
      (e:Expr.t)
    : Expr.t =
  if String.length c > 3 && String.equal (String.sub c 0 3) "Un_" then
    let c = String.sub c 3 (String.length c - 3) in
    Expr.mk_unctor (Id.create c) e
  else
    Expr.mk_ctor (Id.create c) e

# 151 "src/parser.ml"

let rec _menhir_goto_pattern_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.Pattern.t list) -> 'ttv_return =
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
        | LID _v ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
        | LPAREN ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState100
        | UID _v ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
        | WILDCARD ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState100
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState100)
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (p : (Lang.Pattern.t))), _, (ps : (Lang.Pattern.t list))) = _menhir_stack in
        let _v : (Lang.Pattern.t) = 
# 338 "src/parser.mly"
    ( Pattern.Tuple (p :: List.rev ps) )
# 185 "src/parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_pattern : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.Pattern.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LID _v ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
            | LPAREN ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState97
            | UID _v ->
                _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
            | WILDCARD ->
                _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState97
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState97)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (ps : (Lang.Pattern.t list))), _, (p : (Lang.Pattern.t))) = _menhir_stack in
        let _v : (Lang.Pattern.t list) = 
# 346 "src/parser.mly"
    ( p::ps )
# 234 "src/parser.ml"
         in
        _menhir_goto_pattern_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState97 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (p : (Lang.Pattern.t))) = _menhir_stack in
        let _v : (Lang.Pattern.t list) = 
# 344 "src/parser.mly"
    ( [p] )
# 244 "src/parser.ml"
         in
        _menhir_goto_pattern_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (c : (
# 22 "src/parser.mly"
       (string)
# 253 "src/parser.ml"
        ))), _, (p : (Lang.Pattern.t))) = _menhir_stack in
        let _v : (Lang.Pattern.t) = 
# 332 "src/parser.mly"
    ( (Pattern.Ctor (Id.create c,p)) )
# 258 "src/parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
    | MenhirState90 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ARR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FIX ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState105
            | FUN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState105
            | INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
            | LID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
            | LPAREN ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState105
            | MATCH ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState105
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState105)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce69 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
    let _v : (Type.t) = 
# 208 "src/parser.mly"
                ( t )
# 304 "src/parser.ml"
     in
    _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_exp_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.Expr.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ARR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | FIX ->
                    _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState147
                | FUN ->
                    _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState147
                | INT _v ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
                | LID _v ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
                | LPAREN ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState147
                | MATCH ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState147
                | UID _v ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState147)
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
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e : (Lang.Expr.t))), _, (es : (Lang.Expr.t list))) = _menhir_stack in
        let _v : (Lang.Expr.t list) = 
# 122 "src/parser.mly"
    ( e::es )
# 364 "src/parser.ml"
         in
        _menhir_goto_nonempty_exp_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_examples : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Lang.Expr.t list * Lang.Expr.t) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUIV ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FIX ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState157
            | FUN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState157
            | INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _v
            | LID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _v
            | LPAREN ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState157
            | MATCH ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState157
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState157)
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (exs : ((Lang.Expr.t list * Lang.Expr.t) list))) = _menhir_stack in
            let _v : (Problem.unprocessed_spec) = 
# 94 "src/parser.mly"
      (Problem.UIOEs exs)
# 408 "src/parser.ml"
             in
            _menhir_goto_spec _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState160 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (ex : (Lang.Expr.t list * Lang.Expr.t))), _, (exs : ((Lang.Expr.t list * Lang.Expr.t) list))) = _menhir_stack in
        let _v : ((Lang.Expr.t list * Lang.Expr.t) list) = 
# 107 "src/parser.mly"
    ( ex::exs )
# 424 "src/parser.ml"
         in
        _menhir_goto_nonempty_examples _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run91 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (Lang.Pattern.t) = 
# 334 "src/parser.mly"
    ( Pattern.Wildcard )
# 437 "src/parser.ml"
     in
    _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v

and _menhir_run92 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 22 "src/parser.mly"
       (string)
# 444 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
    | LPAREN ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | UID _v ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
    | WILDCARD ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState92
    | ARR | COMMA | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (c : (
# 22 "src/parser.mly"
       (string)
# 464 "src/parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.Pattern.t) = 
# 330 "src/parser.mly"
    ( (Pattern.Ctor (Id.create c,Pattern.Wildcard)) )
# 469 "src/parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState92

and _menhir_run93 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | LPAREN ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState93 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (Lang.Pattern.t) = 
# 336 "src/parser.mly"
    ( Pattern.Tuple [] )
# 496 "src/parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
    | UID _v ->
        _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | WILDCARD ->
        _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93

and _menhir_run95 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 21 "src/parser.mly"
       (string)
# 511 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (x : (
# 21 "src/parser.mly"
       (string)
# 519 "src/parser.ml"
    )) = _v in
    let _v : (Lang.Pattern.t) = 
# 340 "src/parser.mly"
    ( Pattern.Var (Id.create x) )
# 524 "src/parser.ml"
     in
    _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v

and _menhir_run84 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.Expr.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState84
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84

and _menhir_goto_typ_variant : _menhir_env -> 'ttv_tail -> _menhir_state -> (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState139 | MenhirState125 | MenhirState13 | MenhirState20 | MenhirState42 | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (t : (Type.t)) = _v in
        let _v : (Type.t) = 
# 179 "src/parser.mly"
                  ( t )
# 562 "src/parser.ml"
         in
        _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ts : (Type.t)) = _v in
        let (_menhir_stack, _menhir_s, (t : (MyStdLib.Id.t * Type.t))) = _menhir_stack in
        let _v : (Type.t) = 
# 186 "src/parser.mly"
    ( Type.mk_variant (t::(Type.destruct_variant_exn ts)) )
# 573 "src/parser.ml"
         in
        _menhir_goto_typ_variant _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_reduce71 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
    let _v : (Type.t) = 
# 210 "src/parser.mly"
                ( t )
# 585 "src/parser.ml"
     in
    _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v

and _menhir_run39 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
    | LPAREN ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | UNIT ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState39
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState39

and _menhir_goto_typ_non_arrow : _menhir_env -> 'ttv_tail -> _menhir_state -> (Type.t) -> 'ttv_return =
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
        | LID _v ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _v
        | LPAREN ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | MU ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | PIPE ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | UNIT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_typ_tuple_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Type.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (ts : (Type.t list)) = _v in
    let _v : (Type.t) = 
# 214 "src/parser.mly"
                      ( Type.mk_tuple ts )
# 646 "src/parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState139 | MenhirState125 | MenhirState13 | MenhirState20 | MenhirState42 | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ARR ->
            _menhir_reduce69 _menhir_env (Obj.magic _menhir_stack)
        | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 174 "src/parser.mly"
                  ( t )
# 663 "src/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 198 "src/parser.mly"
                  ( t )
# 683 "src/parser.ml"
             in
            _menhir_goto_typ_non_variant _menhir_env _menhir_stack _menhir_s _v
        | ARR ->
            _menhir_reduce69 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run28 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState28 _v
    | LPAREN ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState28
    | UNIT ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState28
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState28

and _menhir_goto_spec : _menhir_env -> 'ttv_tail -> _menhir_state -> (Problem.unprocessed_spec) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EOF ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s, (ids : (string list * Declaration.t list))), _, (st : (Type.t))), _, (ds : (Declaration.t list))), _, (s : (Problem.unprocessed_spec))) = _menhir_stack in
        let _v : (Problem.t_unprocessed) = 
# 77 "src/parser.mly"
      ( (fst ids,snd ids,st,ds,s) )
# 727 "src/parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_1 : (Problem.t_unprocessed)) = _v in
        Obj.magic _1
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_nonempty_exp_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.Expr.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (es : (Lang.Expr.t list)) = _v in
    let _v : (Lang.Expr.t list) = 
# 117 "src/parser.mly"
    ( es )
# 748 "src/parser.ml"
     in
    _menhir_goto_exp_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce39 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Lang.Expr.t list) = 
# 118 "src/parser.mly"
    ( [] )
# 757 "src/parser.ml"
     in
    _menhir_goto_exp_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_nonempty_examples : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Lang.Expr.t list * Lang.Expr.t) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (exs : ((Lang.Expr.t list * Lang.Expr.t) list)) = _v in
    let _v : ((Lang.Expr.t list * Lang.Expr.t) list) = 
# 102 "src/parser.mly"
    ( exs )
# 769 "src/parser.ml"
     in
    _menhir_goto_examples _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce13 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : ((Lang.Expr.t list * Lang.Expr.t) list) = 
# 103 "src/parser.mly"
    ( [] )
# 778 "src/parser.ml"
     in
    _menhir_goto_examples _menhir_env _menhir_stack _menhir_s _v

and _menhir_run143 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
    | RBRACKET ->
        _menhir_reduce39 _menhir_env (Obj.magic _menhir_stack) MenhirState143
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143

and _menhir_goto_decl : _menhir_env -> 'ttv_tail -> _menhir_state -> (Declaration.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LET ->
        _menhir_run127 _menhir_env (Obj.magic _menhir_stack) MenhirState134
    | TYPE ->
        _menhir_run123 _menhir_env (Obj.magic _menhir_stack) MenhirState134
    | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LID _ | LPAREN | MATCH | SYNTH | UID _ ->
        _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState134
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState134

and _menhir_goto_branches : _menhir_env -> 'ttv_tail -> ((Lang.Pattern.t * Lang.Expr.t) list) -> 'ttv_return =
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
        | LID _v ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _v
        | LPAREN ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState90
        | UID _v ->
            _menhir_run92 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _v
        | WILDCARD ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack) MenhirState90
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState90)
    | COMMA | DOT | EOF | EQUIV | FATEQ | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | NEQ | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (e : (Lang.Expr.t))), (bs : ((Lang.Pattern.t * Lang.Expr.t) list))) = _menhir_stack in
        let _v : (Lang.Expr.t) = 
# 297 "src/parser.mly"
    ( Expr.mk_match e (List.rev bs) )
# 857 "src/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_exp_comma_list_one : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.Expr.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (e : (Lang.Expr.t))), _, (es : (Lang.Expr.t list))) = _menhir_stack in
            let _v : (Lang.Expr.t) = 
# 299 "src/parser.mly"
    ( Expr.mk_tuple (e :: List.rev es) )
# 886 "src/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState110 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run84 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (c : (
# 22 "src/parser.mly"
       (string)
# 909 "src/parser.ml"
            ))), _, (e : (Lang.Expr.t))), _, (es : (Lang.Expr.t list))) = _menhir_stack in
            let _v : (Lang.Expr.t) = 
# 295 "src/parser.mly"
                                  ( mk_unctor_or_ctor_by_name c (Expr.mk_tuple (e :: List.rev es)) )
# 914 "src/parser.ml"
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

and _menhir_reduce72 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
    let _v : (Type.t) = 
# 211 "src/parser.mly"
                ( t )
# 932 "src/parser.ml"
     in
    _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v

and _menhir_run25 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v
    | LPAREN ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | UNIT ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25

and _menhir_goto_typ_single_variant : _menhir_env -> 'ttv_tail -> _menhir_state -> (MyStdLib.Id.t * Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | PIPE ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState36
    | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (t : (MyStdLib.Id.t * Type.t))) = _menhir_stack in
        let _v : (Type.t) = 
# 188 "src/parser.mly"
    ( Type.mk_variant [t] )
# 967 "src/parser.ml"
         in
        _menhir_goto_typ_variant _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36

and _menhir_goto_typ_non_variant : _menhir_env -> 'ttv_tail -> _menhir_state -> (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (t : (Type.t)) = _v in
    let ((_menhir_stack, _menhir_s), (i : (
# 22 "src/parser.mly"
       (string)
# 983 "src/parser.ml"
    ))) = _menhir_stack in
    let _v : (MyStdLib.Id.t * Type.t) = 
# 192 "src/parser.mly"
    ( (Id.create i,t) )
# 988 "src/parser.ml"
     in
    _menhir_goto_typ_single_variant _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_typ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (t : (Type.t))), _, (t2 : (Type.t))) = _menhir_stack in
        let _v : (Type.t) = 
# 205 "src/parser.mly"
                               ( Type.mk_arrow t t2 )
# 1003 "src/parser.ml"
         in
        (match _menhir_s with
        | MenhirState139 | MenhirState125 | MenhirState13 | MenhirState20 | MenhirState21 | MenhirState42 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (t : (Type.t)) = _v in
            let _v : (Type.t) = 
# 173 "src/parser.mly"
                  ( t )
# 1013 "src/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | MenhirState17 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (t : (Type.t)) = _v in
            let _v : (Type.t) = 
# 197 "src/parser.mly"
                  ( t )
# 1023 "src/parser.ml"
             in
            _menhir_goto_typ_non_variant _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            _menhir_fail ())
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 234 "src/parser.mly"
                        ( t )
# 1041 "src/parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            (match _menhir_s with
            | MenhirState28 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, (ts : (Type.t list))), _, (t : (Type.t))) = _menhir_stack in
                let _v : (Type.t list) = 
# 227 "src/parser.mly"
                                           ( t :: ts )
# 1052 "src/parser.ml"
                 in
                _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
            | MenhirState45 | MenhirState39 | MenhirState25 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
                let _v : (Type.t list) = 
# 224 "src/parser.mly"
                ( [t] )
# 1062 "src/parser.ml"
                 in
                _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
            | MenhirState139 | MenhirState125 | MenhirState13 | MenhirState20 | MenhirState42 | MenhirState21 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | STAR ->
                    _menhir_run39 _menhir_env (Obj.magic _menhir_stack)
                | ARR ->
                    _menhir_reduce71 _menhir_env (Obj.magic _menhir_stack)
                | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
                    let _v : (Type.t) = 
# 176 "src/parser.mly"
                  ( t )
# 1080 "src/parser.ml"
                     in
                    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | MenhirState17 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | STAR ->
                    _menhir_run39 _menhir_env (Obj.magic _menhir_stack)
                | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
                    let _v : (Type.t) = 
# 200 "src/parser.mly"
                  ( t )
# 1102 "src/parser.ml"
                     in
                    _menhir_goto_typ_non_variant _menhir_env _menhir_stack _menhir_s _v
                | ARR ->
                    _menhir_reduce71 _menhir_env (Obj.magic _menhir_stack)
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
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), (i : (
# 21 "src/parser.mly"
       (string)
# 1127 "src/parser.ml"
        ))), _, (t : (Type.t))) = _menhir_stack in
        let _v : (Type.t) = 
# 182 "src/parser.mly"
                       ( Type.mk_mu (Id.create i) t )
# 1132 "src/parser.ml"
         in
        (match _menhir_s with
        | MenhirState139 | MenhirState125 | MenhirState13 | MenhirState20 | MenhirState21 | MenhirState42 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (t : (Type.t)) = _v in
            let _v : (Type.t) = 
# 178 "src/parser.mly"
                  ( t )
# 1142 "src/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | MenhirState17 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (t : (Type.t)) = _v in
            let _v : (Type.t) = 
# 202 "src/parser.mly"
                  ( t )
# 1152 "src/parser.ml"
             in
            _menhir_goto_typ_non_variant _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            _menhir_fail ())
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (x : (
# 21 "src/parser.mly"
       (string)
# 1169 "src/parser.ml"
            ))), _, (t : (Type.t))) = _menhir_stack in
            let _v : (Param.t) = 
# 261 "src/parser.mly"
    ( (Id.create x, t) )
# 1174 "src/parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            (match _menhir_s with
            | MenhirState10 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ARR ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | FIX ->
                        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState62
                    | FUN ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState62
                    | INT _v ->
                        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
                    | LID _v ->
                        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
                    | LPAREN ->
                        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState62
                    | MATCH ->
                        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState62
                    | UID _v ->
                        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | MenhirState63 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | EQ ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | FIX ->
                        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                    | FUN ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                    | INT _v ->
                        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
                    | LID _v ->
                        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
                    | LPAREN ->
                        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                    | MATCH ->
                        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                    | UID _v ->
                        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65)
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
    | MenhirState125 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), (i : (
# 21 "src/parser.mly"
       (string)
# 1260 "src/parser.ml"
        ))), _, (t : (Type.t))) = _menhir_stack in
        let _v : (Declaration.t) = 
# 136 "src/parser.mly"
    ( Declaration.type_dec (Id.create i) t )
# 1265 "src/parser.ml"
         in
        _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SATISFYING ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LET ->
                _menhir_run127 _menhir_env (Obj.magic _menhir_stack) MenhirState141
            | TYPE ->
                _menhir_run123 _menhir_env (Obj.magic _menhir_stack) MenhirState141
            | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LID _ | LPAREN | MATCH | UID _ ->
                _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState141
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState141)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce70 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
    let _v : (Type.t) = 
# 209 "src/parser.mly"
                ( t )
# 1303 "src/parser.ml"
     in
    _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v

and _menhir_run45 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _v
    | LPAREN ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState45
    | UNIT ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState45
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState45

and _menhir_goto_typ_tuple_list_one : _menhir_env -> 'ttv_tail -> _menhir_state -> (Type.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack)
        | ARR | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (t : (Type.t))), _, (ts : (Type.t list))) = _menhir_stack in
            let _v : (Type.t list) = 
# 220 "src/parser.mly"
                                           ( t :: List.rev ts )
# 1340 "src/parser.ml"
             in
            _menhir_goto_typ_tuple_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack)
        | ARR | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (t : (Type.t))), _, (ts : (Type.t list))) = _menhir_stack in
            let _v : (Type.t list) = 
# 219 "src/parser.mly"
                                           ( t :: List.rev ts )
# 1362 "src/parser.ml"
             in
            _menhir_goto_typ_tuple_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack)
        | ARR | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (t : (Type.t))), _, (ts : (Type.t list))) = _menhir_stack in
            let _v : (Type.t list) = 
# 218 "src/parser.mly"
                                           ( t :: List.rev ts )
# 1384 "src/parser.ml"
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

and _menhir_goto_decl_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Declaration.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (is : (string list))), _, (ds : (Declaration.t list))) = _menhir_stack in
        let _v : (string list * Declaration.t list) = 
# 85 "src/parser.mly"
      ( (is,ds) )
# 1407 "src/parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState115 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | EOF ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (ids : (string list * Declaration.t list))) = _menhir_stack in
                let _v : (string list * Declaration.t list) = 
# 81 "src/parser.mly"
      ( ids )
# 1423 "src/parser.ml"
                 in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_1 : (string list * Declaration.t list)) = _v in
                Obj.magic _1
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState136 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | SYNTH ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LID _v ->
                    _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
                | LPAREN ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState139
                | MU ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState139
                | PIPE ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState139
                | UNIT ->
                    _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState139
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState139)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            _menhir_fail ())
    | MenhirState134 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (d : (Declaration.t))), _, (ds : (Declaration.t list))) = _menhir_stack in
        let _v : (Declaration.t list) = 
# 132 "src/parser.mly"
    ( d::ds )
# 1474 "src/parser.ml"
         in
        _menhir_goto_decl_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState141 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FIX ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState142
        | FUN ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState142
        | INT _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _v
        | LBRACKET ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState142
        | LID _v ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _v
        | LPAREN ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState142
        | MATCH ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState142
        | UID _v ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _v
        | EOF | EQUIV ->
            _menhir_reduce13 _menhir_env (Obj.magic _menhir_stack) MenhirState142
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState142)
    | _ ->
        _menhir_fail ()

and _menhir_goto_exp_app_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.Expr.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState76
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
    | COMMA | DOT | EOF | EQUIV | FATEQ | NEQ | PIPE | RBRACKET | RPAREN | SEMI | WITH ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e : (Lang.Expr.t))), _, (es : (Lang.Expr.t list))) = _menhir_stack in
        let _v : (Lang.Expr.t) = 
# 249 "src/parser.mly"
    ( appify e (List.rev es) )
# 1534 "src/parser.ml"
         in
        _menhir_goto_exp_app _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState76

and _menhir_goto_exp_app : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.Expr.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (e : (Lang.Expr.t)) = _v in
    let _v : (Lang.Expr.t) = 
# 245 "src/parser.mly"
    ( e )
# 1550 "src/parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FIX ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState81
            | FUN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState81
            | INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
            | LID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
            | LPAREN ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState81
            | MATCH ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState81
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState81)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Lang.Expr.t))) = _menhir_stack in
            let _v : (Lang.Expr.t) = 
# 307 "src/parser.mly"
    ( e )
# 1590 "src/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (es : (Lang.Expr.t list))), _, (e : (Lang.Expr.t))) = _menhir_stack in
        let _v : (Lang.Expr.t list) = 
# 315 "src/parser.mly"
    ( e :: es )
# 1606 "src/parser.ml"
         in
        _menhir_goto_exp_comma_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState110 | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (e : (Lang.Expr.t))) = _menhir_stack in
        let _v : (Lang.Expr.t list) = 
# 313 "src/parser.mly"
    ( [e] )
# 1616 "src/parser.ml"
         in
        _menhir_goto_exp_comma_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _v : ((Lang.Pattern.t * Lang.Expr.t) list) = 
# 320 "src/parser.mly"
    ( [] )
# 1631 "src/parser.ml"
             in
            _menhir_goto_branches _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, (p : (Lang.Pattern.t))), _, (e : (Lang.Expr.t))) = _menhir_stack in
        let _v : (Lang.Pattern.t * Lang.Expr.t) = 
# 326 "src/parser.mly"
    ( (p, e) )
# 1647 "src/parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (b : (Lang.Pattern.t * Lang.Expr.t)) = _v in
        let (_menhir_stack, (bs : ((Lang.Pattern.t * Lang.Expr.t) list))) = _menhir_stack in
        let _v : ((Lang.Pattern.t * Lang.Expr.t) list) = 
# 322 "src/parser.mly"
    ( b::bs )
# 1656 "src/parser.ml"
         in
        _menhir_goto_branches _menhir_env _menhir_stack _v
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FIX ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | FUN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
            | LID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
            | LPAREN ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | MATCH ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState110)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (c : (
# 22 "src/parser.mly"
       (string)
# 1694 "src/parser.ml"
            ))), _, (e : (Lang.Expr.t))) = _menhir_stack in
            let _v : (Lang.Expr.t) = 
# 287 "src/parser.mly"
                     ( mk_unctor_or_ctor_by_name c e )
# 1699 "src/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (_1 : (Lang.Expr.t))) = _menhir_stack in
        Obj.magic _1
    | MenhirState129 ->
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
                let (((_menhir_stack, _menhir_s), (i : (
# 21 "src/parser.mly"
       (string)
# 1730 "src/parser.ml"
                ))), _, (e : (Lang.Expr.t))) = _menhir_stack in
                let _v : (Declaration.t) = 
# 138 "src/parser.mly"
    ( Declaration.expr_dec (Id.create i) e )
# 1735 "src/parser.ml"
                 in
                _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
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
    | MenhirState147 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (es : (Lang.Expr.t list))), _, (e : (Lang.Expr.t))) = _menhir_stack in
        let _v : (Lang.Expr.t list * Lang.Expr.t) = 
# 113 "src/parser.mly"
    ( (es,e) )
# 1757 "src/parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACKET ->
                _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState160
            | EOF | EQUIV ->
                _menhir_reduce13 _menhir_env (Obj.magic _menhir_stack) MenhirState160
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState160)
        | EOF | EQUIV ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (ex : (Lang.Expr.t list * Lang.Expr.t))) = _menhir_stack in
            let _v : ((Lang.Expr.t list * Lang.Expr.t) list) = 
# 109 "src/parser.mly"
    ( [ex] )
# 1783 "src/parser.ml"
             in
            _menhir_goto_nonempty_examples _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState150 | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FIX ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | FUN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _v
            | LID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _v
            | LPAREN ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | MATCH ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _v
            | RBRACKET ->
                _menhir_reduce39 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState150)
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Lang.Expr.t))) = _menhir_stack in
            let _v : (Lang.Expr.t list) = 
# 124 "src/parser.mly"
    ( [e] )
# 1828 "src/parser.ml"
             in
            _menhir_goto_nonempty_exp_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (e : (Lang.Expr.t))) = _menhir_stack in
        let _v : (Problem.unprocessed_spec) = 
# 98 "src/parser.mly"
      (Problem.UPost e)
# 1844 "src/parser.ml"
         in
        _menhir_goto_spec _menhir_env _menhir_stack _menhir_s _v
    | MenhirState157 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (exs : ((Lang.Expr.t list * Lang.Expr.t) list))), _, (e : (Lang.Expr.t))) = _menhir_stack in
        let _v : (Problem.unprocessed_spec) = 
# 96 "src/parser.mly"
      (Problem.init_uioes := exs; Problem.UEquiv e)
# 1854 "src/parser.ml"
         in
        _menhir_goto_spec _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run67 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.Expr.t) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState67
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState67
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState67
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState67
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState67

and _menhir_run69 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.Expr.t) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState69
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState69

and _menhir_run71 : _menhir_env -> 'ttv_tail * _menhir_state * (Lang.Expr.t) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INT _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (n : (
# 26 "src/parser.mly"
       (int)
# 1923 "src/parser.ml"
        )) = _v in
        let ((_menhir_stack, _menhir_s, (e : (Lang.Expr.t))), _) = _menhir_stack in
        let _v : (Lang.Expr.t) = 
# 301 "src/parser.mly"
    ( Expr.mk_proj n e )
# 1929 "src/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run14 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (Type.t) = 
# 237 "src/parser.mly"
         ( Type.mk_tuple [] )
# 1946 "src/parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState139 | MenhirState125 | MenhirState13 | MenhirState20 | MenhirState42 | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | ARR ->
            _menhir_reduce72 _menhir_env (Obj.magic _menhir_stack)
        | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 177 "src/parser.mly"
                  ( t )
# 1965 "src/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState45 | MenhirState39 | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
        let _v : (Type.t list) = 
# 225 "src/parser.mly"
                ( [t] )
# 1981 "src/parser.ml"
         in
        _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState28 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (ts : (Type.t list))), _, (t : (Type.t))) = _menhir_stack in
        let _v : (Type.t list) = 
# 228 "src/parser.mly"
                                           ( t :: ts )
# 1991 "src/parser.ml"
         in
        _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 201 "src/parser.mly"
                  ( t )
# 2007 "src/parser.ml"
             in
            _menhir_goto_typ_non_variant _menhir_env _menhir_stack _menhir_s _v
        | ARR ->
            _menhir_reduce72 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run15 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
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
            | LID _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
            | LPAREN ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState17
            | MU ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState17
            | UNIT ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState17
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17)
        | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), (i : (
# 22 "src/parser.mly"
       (string)
# 2055 "src/parser.ml"
            ))) = _menhir_stack in
            let _v : (MyStdLib.Id.t * Type.t) = 
# 194 "src/parser.mly"
    ( (Id.create i,Type.mk_tuple []) )
# 2060 "src/parser.ml"
             in
            _menhir_goto_typ_single_variant _menhir_env _menhir_stack _menhir_s _v
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

and _menhir_run18 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | DOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LID _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
            | LPAREN ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | MU ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | PIPE ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | UNIT ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20)
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

and _menhir_run21 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v
    | LPAREN ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState21
    | MU ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState21
    | PIPE ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState21
    | UNIT ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState21
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState21

and _menhir_run22 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 21 "src/parser.mly"
       (string)
# 2144 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (d : (
# 21 "src/parser.mly"
       (string)
# 2152 "src/parser.ml"
    )) = _v in
    let _v : (Type.t) = 
# 231 "src/parser.mly"
          ( Type.mk_named (Id.create d) )
# 2157 "src/parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState28 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (ts : (Type.t list))), _, (t : (Type.t))) = _menhir_stack in
        let _v : (Type.t list) = 
# 226 "src/parser.mly"
                                           ( t :: ts )
# 2168 "src/parser.ml"
         in
        _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState45 | MenhirState39 | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
        let _v : (Type.t list) = 
# 223 "src/parser.mly"
                ( [t] )
# 2178 "src/parser.ml"
         in
        _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState139 | MenhirState125 | MenhirState13 | MenhirState20 | MenhirState21 | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack)
        | ARR ->
            _menhir_reduce70 _menhir_env (Obj.magic _menhir_stack)
        | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 175 "src/parser.mly"
                  ( t )
# 2196 "src/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack)
        | EOF | EQUIV | FIX | FUN | INT _ | LBRACKET | LET | LID _ | LPAREN | MATCH | PIPE | RPAREN | SATISFYING | SYNTH | TYPE | UID _ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 199 "src/parser.mly"
                  ( t )
# 2218 "src/parser.ml"
             in
            _menhir_goto_typ_non_variant _menhir_env _menhir_stack _menhir_s _v
        | ARR ->
            _menhir_reduce70 _menhir_env (Obj.magic _menhir_stack)
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

and _menhir_reduce9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Declaration.t list) = 
# 130 "src/parser.mly"
    ( [] )
# 2242 "src/parser.ml"
     in
    _menhir_goto_decl_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_run123 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
            | LID _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _v
            | LPAREN ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | MU ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | PIPE ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | UNIT ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState125)
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

and _menhir_run127 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
            | FIX ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | FUN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _v
            | LID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _v
            | LPAREN ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | MATCH ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState129)
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

and _menhir_goto_exp_base : _menhir_env -> 'ttv_tail -> _menhir_state -> (Lang.Expr.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | FATEQ ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | NEQ ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | COMMA | EOF | EQUIV | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | PIPE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (a : (Param.t))), _, (e : (Lang.Expr.t))) = _menhir_stack in
            let _v : (Lang.Expr.t) = 
# 275 "src/parser.mly"
    ( Expr.mk_fix (fst a) (snd a) e )
# 2359 "src/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState66)
    | MenhirState67 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | FATEQ ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | NEQ ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | COMMA | EOF | EQUIV | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | PIPE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Lang.Expr.t))), _), _, (e2 : (Lang.Expr.t))) = _menhir_stack in
            let _v : (Lang.Expr.t) = 
# 305 "src/parser.mly"
    ( Expr.mk_eq false e1 e2 )
# 2383 "src/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState68)
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | FATEQ ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | NEQ ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | COMMA | EOF | EQUIV | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | PIPE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Lang.Expr.t))), _), _, (e2 : (Lang.Expr.t))) = _menhir_stack in
            let _v : (Lang.Expr.t) = 
# 303 "src/parser.mly"
    ( Expr.mk_eq true e1 e2 )
# 2407 "src/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState70)
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState73
        | FATEQ ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState73
        | NEQ ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState73
        | COMMA | EOF | EQUIV | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | PIPE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (x : (Param.t))), _, (e : (Lang.Expr.t))) = _menhir_stack in
            let _v : (Lang.Expr.t) = 
# 273 "src/parser.mly"
    ( Expr.mk_func x e )
# 2431 "src/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState73)
    | MenhirState157 | MenhirState142 | MenhirState150 | MenhirState143 | MenhirState147 | MenhirState129 | MenhirState0 | MenhirState110 | MenhirState3 | MenhirState105 | MenhirState5 | MenhirState81 | MenhirState84 | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | FATEQ ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | FIX ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | FUN ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | INT _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
        | LID _v ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
        | LPAREN ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | MATCH ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | NEQ ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | UID _v ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
        | COMMA | EOF | EQUIV | PIPE | RBRACKET | RPAREN | SEMI | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Lang.Expr.t))) = _menhir_stack in
            let _v : (Lang.Expr.t) = 
# 251 "src/parser.mly"
    ( e )
# 2469 "src/parser.ml"
             in
            _menhir_goto_exp_app _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState74)
    | MenhirState74 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | FATEQ ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | NEQ ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | COMMA | EOF | EQUIV | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | PIPE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Lang.Expr.t))) = _menhir_stack in
            let _v : (Lang.Expr.t list) = 
# 255 "src/parser.mly"
    ( [e] )
# 2493 "src/parser.ml"
             in
            _menhir_goto_exp_app_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75)
    | MenhirState76 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | FATEQ ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | NEQ ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | COMMA | EOF | EQUIV | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | PIPE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (es : (Lang.Expr.t list))), _, (e : (Lang.Expr.t))) = _menhir_stack in
            let _v : (Lang.Expr.t list) = 
# 257 "src/parser.mly"
    ( e::es )
# 2517 "src/parser.ml"
             in
            _menhir_goto_exp_app_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77)
    | _ ->
        _menhir_fail ()

and _menhir_run11 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
            | LID _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
            | LPAREN ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState13
            | MU ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState13
            | PIPE ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState13
            | UNIT ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState13
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState13)
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

and _menhir_goto_imports : _menhir_env -> 'ttv_tail -> _menhir_state -> (string list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState117 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), (s : (
# 23 "src/parser.mly"
       (string)
# 2581 "src/parser.ml"
        ))), _, (is : (string list))) = _menhir_stack in
        let _v : (string list) = 
# 89 "src/parser.mly"
      ( s::is )
# 2586 "src/parser.ml"
         in
        _menhir_goto_imports _menhir_env _menhir_stack _menhir_s _v
    | MenhirState136 | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LET ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack) MenhirState122
        | TYPE ->
            _menhir_run123 _menhir_env (Obj.magic _menhir_stack) MenhirState122
        | EOF | SYNTH ->
            _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState122
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState122)
    | _ ->
        _menhir_fail ()

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 22 "src/parser.mly"
       (string)
# 2610 "src/parser.ml"
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
# 21 "src/parser.mly"
       (string)
# 2624 "src/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s, (c : (
# 22 "src/parser.mly"
       (string)
# 2629 "src/parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.Expr.t) = 
# 291 "src/parser.mly"
              ( mk_unctor_or_ctor_by_name c (Expr.mk_var (Id.create x)) )
# 2634 "src/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FIX ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState3
        | FUN ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState3
        | INT _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
        | LID _v ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
        | LPAREN ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState3
        | MATCH ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState3
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState3 in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (c : (
# 22 "src/parser.mly"
       (string)
# 2662 "src/parser.ml"
            ))) = _menhir_stack in
            let _v : (Lang.Expr.t) = 
# 293 "src/parser.mly"
        ( mk_unctor_or_ctor_by_name c Expr.mk_unit )
# 2667 "src/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | UID _v ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3)
    | UID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (c2 : (
# 22 "src/parser.mly"
       (string)
# 2683 "src/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s, (c1 : (
# 22 "src/parser.mly"
       (string)
# 2688 "src/parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.Expr.t) = 
# 289 "src/parser.mly"
                ( mk_unctor_or_ctor_by_name c1 (mk_unctor_or_ctor_by_name c2 Expr.mk_unit) )
# 2693 "src/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | COMMA | DOT | EOF | EQUIV | FATEQ | FIX | FUN | INT _ | MATCH | NEQ | PIPE | RBRACKET | RPAREN | SEMI | WITH ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (c : (
# 22 "src/parser.mly"
       (string)
# 2701 "src/parser.ml"
        ))) = _menhir_stack in
        let _v : (Lang.Expr.t) = 
# 283 "src/parser.mly"
    (
      mk_unctor_or_ctor_by_name c Expr.mk_unit
    )
# 2708 "src/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState5

and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState6 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (Lang.Expr.t) = 
# 309 "src/parser.mly"
    ( Expr.mk_unit )
# 2770 "src/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 21 "src/parser.mly"
       (string)
# 2783 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (x : (
# 21 "src/parser.mly"
       (string)
# 2791 "src/parser.ml"
    )) = _v in
    let _v : (Lang.Expr.t) = 
# 271 "src/parser.mly"
    ( Expr.mk_var (Id.create x) )
# 2796 "src/parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 26 "src/parser.mly"
       (int)
# 2803 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (c : (
# 26 "src/parser.mly"
       (int)
# 2811 "src/parser.ml"
    )) = _v in
    let _v : (Lang.Expr.t) = 
# 281 "src/parser.mly"
    ( Expr.from_int c )
# 2816 "src/parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState10
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState10

and _menhir_run63 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState63
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState160 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState157 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState147 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState141 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState136 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState134 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState125 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState117 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState110 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState97 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState90 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState76 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState74 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState73 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState68 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState67 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState66 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState28 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_reduce41 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (string list) = 
# 90 "src/parser.mly"
      ( [] )
# 3059 "src/parser.ml"
     in
    _menhir_goto_imports _menhir_env _menhir_stack _menhir_s _v

and _menhir_run116 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | STR _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INCLUDE ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState117
        | EOF | LET | SYNTH | TYPE ->
            _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState117
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState117)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

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

and exp : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Lang.Expr.t) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

and imports_decls_start : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (string list * Declaration.t list) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INCLUDE ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | EOF | LET | TYPE ->
        _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState115
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState115)

and unprocessed_problem : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Problem.t_unprocessed) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | INCLUDE ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | LET | SYNTH | TYPE ->
        _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState136)

# 269 "<standard.mly>"
  

# 3178 "src/parser.ml"
