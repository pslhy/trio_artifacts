
module MenhirBasics = struct
  
  exception Error
  
  let _eRR : exn =
    Error
  
  type token = 
    | WITH
    | WILDCARD
    | UNIT
    | UID of (
# 22 "trio/parser.mly"
       (string)
# 17 "trio/parser.ml"
  )
    | TYPE
    | SYNTH
    | STR of (
# 23 "trio/parser.mly"
       (string)
# 24 "trio/parser.ml"
  )
    | STAR
    | SEMI
    | SATISFYING
    | RPAREN
    | RBRACKET
    | PIPE
    | OF
    | NEQ
    | MATCH
    | LPAREN
    | LID of (
# 21 "trio/parser.mly"
       (string)
# 39 "trio/parser.ml"
  )
    | LET
    | LBRACKET
    | INT of (
# 26 "trio/parser.mly"
       (int)
# 46 "trio/parser.ml"
  )
    | INCLUDE
    | FUN
    | FIX
    | FATEQ
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
  | MenhirState150
  | MenhirState143
  | MenhirState140
  | MenhirState136
  | MenhirState135
  | MenhirState133
  | MenhirState130
  | MenhirState128
  | MenhirState123
  | MenhirState119
  | MenhirState116
  | MenhirState111
  | MenhirState109
  | MenhirState104
  | MenhirState99
  | MenhirState94
  | MenhirState91
  | MenhirState87
  | MenhirState86
  | MenhirState84
  | MenhirState78
  | MenhirState75
  | MenhirState71
  | MenhirState70
  | MenhirState69
  | MenhirState68
  | MenhirState67
  | MenhirState64
  | MenhirState63
  | MenhirState62
  | MenhirState61
  | MenhirState60
  | MenhirState59
  | MenhirState57
  | MenhirState56
  | MenhirState41
  | MenhirState39
  | MenhirState36
  | MenhirState33
  | MenhirState25
  | MenhirState22
  | MenhirState18
  | MenhirState17
  | MenhirState13
  | MenhirState10
  | MenhirState6
  | MenhirState5
  | MenhirState3
  | MenhirState0

# 1 "trio/parser.mly"
  
open Expr
open Vocab

let rec appify (e:Expr.t) (es:Expr.t list) : Expr.t =
  match es with
  | [] -> e
  | e'::es -> appify (App (e, e')) es

let mk_unctor_or_ctor_by_name
      (c:string)
      (e:Expr.t)
    : Expr.t =
  if String.length c > 3 && String.equal (String.sub c 0 3) "Un_" then
    let c = String.sub c 3 (String.length c - 3) in
    Unctor (c, e)
  else
    Ctor (c, e)

# 141 "trio/parser.ml"

let rec _menhir_goto_pattern_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Expr.Pattern.t list) -> 'ttv_return =
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
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
        | LPAREN ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState94
        | UID _v ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
        | WILDCARD ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState94
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState94)
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (p : (Expr.Pattern.t))), _, (ps : (Expr.Pattern.t list))) = _menhir_stack in
        let _v : (Expr.Pattern.t) = 
# 287 "trio/parser.mly"
    ( Pattern.Tuple (p :: List.rev ps) )
# 175 "trio/parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_pattern : _menhir_env -> 'ttv_tail -> _menhir_state -> (Expr.Pattern.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState87 ->
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
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
            | LPAREN ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | UID _v ->
                _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
            | WILDCARD ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState94 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (ps : (Expr.Pattern.t list))), _, (p : (Expr.Pattern.t))) = _menhir_stack in
        let _v : (Expr.Pattern.t list) = 
# 295 "trio/parser.mly"
    ( p::ps )
# 224 "trio/parser.ml"
         in
        _menhir_goto_pattern_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (p : (Expr.Pattern.t))) = _menhir_stack in
        let _v : (Expr.Pattern.t list) = 
# 293 "trio/parser.mly"
    ( [p] )
# 234 "trio/parser.ml"
         in
        _menhir_goto_pattern_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState86 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (c : (
# 22 "trio/parser.mly"
       (string)
# 243 "trio/parser.ml"
        ))), _, (p : (Expr.Pattern.t))) = _menhir_stack in
        let _v : (Expr.Pattern.t) = 
# 281 "trio/parser.mly"
    ( (Pattern.Ctor (c, p)) )
# 248 "trio/parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
    | MenhirState84 ->
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
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | FUN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
            | LID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
            | LPAREN ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | MATCH ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState99)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce65 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
    let _v : (Type.t) = 
# 161 "trio/parser.mly"
                ( t )
# 294 "trio/parser.ml"
     in
    _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_exp_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Expr.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState136 ->
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
                    _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState140
                | FUN ->
                    _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState140
                | INT _v ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v
                | LID _v ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v
                | LPAREN ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState140
                | MATCH ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState140
                | UID _v ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState140)
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
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e : (Expr.t))), _, (es : (Expr.t list))) = _menhir_stack in
        let _v : (Expr.t list) = 
# 112 "trio/parser.mly"
    ( e::es )
# 354 "trio/parser.ml"
         in
        _menhir_goto_nonempty_exp_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_examples : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Expr.t list * Expr.t) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState135 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (exs : ((Expr.t list * Expr.t) list)) = _v in
        let _v : (Specification.unprocessed_spec) = 
# 88 "trio/parser.mly"
      (Specification.UIOEs exs)
# 370 "trio/parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (ids : (string list * Expr.declaration list))), _, (st : (Type.t))), _, (s : (Specification.unprocessed_spec))) = _menhir_stack in
            let _v : (Specification.t_unprocessed) = 
# 71 "trio/parser.mly"
      ( (fst ids,snd ids,st,s) )
# 384 "trio/parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : (Specification.t_unprocessed)) = _v in
            Obj.magic _1
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (exs : ((Expr.t list * Expr.t) list)) = _v in
        let (_menhir_stack, _menhir_s, (ex : (Expr.t list * Expr.t))) = _menhir_stack in
        let _v : ((Expr.t list * Expr.t) list) = 
# 97 "trio/parser.mly"
    ( ex::exs )
# 404 "trio/parser.ml"
         in
        _menhir_goto_nonempty_examples _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run85 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (Expr.Pattern.t) = 
# 283 "trio/parser.mly"
    ( Pattern.Wildcard )
# 417 "trio/parser.ml"
     in
    _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v

and _menhir_run86 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 22 "trio/parser.mly"
       (string)
# 424 "trio/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _v
    | LPAREN ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState86
    | UID _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _v
    | WILDCARD ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState86
    | ARR | COMMA | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (c : (
# 22 "trio/parser.mly"
       (string)
# 444 "trio/parser.ml"
        ))) = _menhir_stack in
        let _v : (Expr.Pattern.t) = 
# 279 "trio/parser.mly"
    ( (Pattern.Ctor (c, Pattern.Wildcard)) )
# 449 "trio/parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState86

and _menhir_run87 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
    | LPAREN ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState87
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState87 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (Expr.Pattern.t) = 
# 285 "trio/parser.mly"
    ( Pattern.Tuple [] )
# 476 "trio/parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
    | UID _v ->
        _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
    | WILDCARD ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState87
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState87

and _menhir_run89 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 21 "trio/parser.mly"
       (string)
# 491 "trio/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (x : (
# 21 "trio/parser.mly"
       (string)
# 499 "trio/parser.ml"
    )) = _v in
    let _v : (Expr.Pattern.t) = 
# 289 "trio/parser.mly"
    ( Pattern.Var x )
# 504 "trio/parser.ml"
     in
    _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v

and _menhir_run78 : _menhir_env -> 'ttv_tail * _menhir_state * (Expr.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState78
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78

and _menhir_goto_typ_variant : _menhir_env -> 'ttv_tail -> _menhir_state -> (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState133 | MenhirState119 | MenhirState13 | MenhirState39 | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (t : (Type.t)) = _v in
        let _v : (Type.t) = 
# 136 "trio/parser.mly"
                  ( t )
# 542 "trio/parser.ml"
         in
        _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ts : (Type.t)) = _v in
        let (_menhir_stack, _menhir_s, (t : (string * Type.t))) = _menhir_stack in
        let _v : (Type.t) = 
# 140 "trio/parser.mly"
    ( Type.Variant (t::(Type.destruct_variant ts)) )
# 553 "trio/parser.ml"
         in
        _menhir_goto_typ_variant _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_reduce67 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
    let _v : (Type.t) = 
# 163 "trio/parser.mly"
                ( t )
# 565 "trio/parser.ml"
     in
    _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v

and _menhir_run36 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v
    | LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState36
    | UNIT ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState36
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36

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
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
        | LPAREN ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState39
        | PIPE ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState39
        | UNIT ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState39
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState39)
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
# 167 "trio/parser.mly"
                      ( Type.Tuple ts )
# 624 "trio/parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState133 | MenhirState119 | MenhirState13 | MenhirState39 | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ARR ->
            _menhir_reduce65 _menhir_env (Obj.magic _menhir_stack)
        | EOF | LET | PIPE | RPAREN | SATISFYING | SYNTH | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 132 "trio/parser.mly"
                  ( t )
# 641 "trio/parser.ml"
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
        | EOF | LET | PIPE | RPAREN | SATISFYING | SYNTH | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 152 "trio/parser.mly"
                  ( t )
# 661 "trio/parser.ml"
             in
            _menhir_goto_typ_non_variant _menhir_env _menhir_stack _menhir_s _v
        | ARR ->
            _menhir_reduce65 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run25 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v
    | LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | UNIT ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState25
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25

and _menhir_goto_nonempty_exp_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Expr.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (es : (Expr.t list)) = _v in
    let _v : (Expr.t list) = 
# 107 "trio/parser.mly"
    ( es )
# 699 "trio/parser.ml"
     in
    _menhir_goto_exp_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce39 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Expr.t list) = 
# 108 "trio/parser.mly"
    ( [] )
# 708 "trio/parser.ml"
     in
    _menhir_goto_exp_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_nonempty_examples : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Expr.t list * Expr.t) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (exs : ((Expr.t list * Expr.t) list)) = _v in
    let _v : ((Expr.t list * Expr.t) list) = 
# 92 "trio/parser.mly"
    ( exs )
# 720 "trio/parser.ml"
     in
    _menhir_goto_examples _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce13 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : ((Expr.t list * Expr.t) list) = 
# 93 "trio/parser.mly"
    ( [] )
# 729 "trio/parser.ml"
     in
    _menhir_goto_examples _menhir_env _menhir_stack _menhir_s _v

and _menhir_run136 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _v
    | RBRACKET ->
        _menhir_reduce39 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState136

and _menhir_goto_decl : _menhir_env -> 'ttv_tail -> _menhir_state -> (Expr.declaration) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LET ->
        _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState128
    | TYPE ->
        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState128
    | EOF | SYNTH ->
        _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState128
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState128

and _menhir_goto_branches : _menhir_env -> 'ttv_tail -> ((Expr.Pattern.t * Expr.t) list) -> 'ttv_return =
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
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
        | LPAREN ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | UID _v ->
            _menhir_run86 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
        | WILDCARD ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84)
    | COMMA | DOT | EOF | FATEQ | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | NEQ | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (e : (Expr.t))), (bs : ((Expr.Pattern.t * Expr.t) list))) = _menhir_stack in
        let _v : (Expr.t) = 
# 246 "trio/parser.mly"
    ( Expr.Match (e, (List.rev bs)) )
# 808 "trio/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_exp_comma_list_one : _menhir_env -> 'ttv_tail -> _menhir_state -> (Expr.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (e : (Expr.t))), _, (es : (Expr.t list))) = _menhir_stack in
            let _v : (Expr.t) = 
# 248 "trio/parser.mly"
    ( Expr.Tuple (e :: List.rev es) )
# 837 "trio/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState104 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            _menhir_run78 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (c : (
# 22 "trio/parser.mly"
       (string)
# 860 "trio/parser.ml"
            ))), _, (e : (Expr.t))), _, (es : (Expr.t list))) = _menhir_stack in
            let _v : (Expr.t) = 
# 244 "trio/parser.mly"
    ( mk_unctor_or_ctor_by_name c (Expr.Tuple (e :: List.rev es)) )
# 865 "trio/parser.ml"
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

and _menhir_reduce68 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
    let _v : (Type.t) = 
# 164 "trio/parser.mly"
                ( t )
# 883 "trio/parser.ml"
     in
    _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v

and _menhir_run22 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | UNIT ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState22

and _menhir_goto_typ_single_variant : _menhir_env -> 'ttv_tail -> _menhir_state -> (string * Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | PIPE ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState33
    | EOF | LET | RPAREN | SATISFYING | SYNTH | TYPE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (t : (string * Type.t))) = _menhir_stack in
        let _v : (Type.t) = 
# 142 "trio/parser.mly"
    ( Type.Variant [t] )
# 918 "trio/parser.ml"
         in
        _menhir_goto_typ_variant _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33

and _menhir_goto_typ_non_variant : _menhir_env -> 'ttv_tail -> _menhir_state -> (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (t : (Type.t)) = _v in
    let ((_menhir_stack, _menhir_s), (i : (
# 22 "trio/parser.mly"
       (string)
# 934 "trio/parser.ml"
    ))) = _menhir_stack in
    let _v : (string * Type.t) = 
# 146 "trio/parser.mly"
    ( (i,t) )
# 939 "trio/parser.ml"
     in
    _menhir_goto_typ_single_variant _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_typ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (t : (Type.t))), _, (t2 : (Type.t))) = _menhir_stack in
        let _v : (Type.t) = 
# 158 "trio/parser.mly"
                               ( Type.Arrow (t, t2) )
# 954 "trio/parser.ml"
         in
        (match _menhir_s with
        | MenhirState133 | MenhirState119 | MenhirState13 | MenhirState18 | MenhirState39 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (t : (Type.t)) = _v in
            let _v : (Type.t) = 
# 131 "trio/parser.mly"
                  ( t )
# 964 "trio/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | MenhirState17 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (t : (Type.t)) = _v in
            let _v : (Type.t) = 
# 151 "trio/parser.mly"
                  ( t )
# 974 "trio/parser.ml"
             in
            _menhir_goto_typ_non_variant _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            _menhir_fail ())
    | MenhirState18 ->
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
# 187 "trio/parser.mly"
                        ( t )
# 992 "trio/parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            (match _menhir_s with
            | MenhirState25 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, (ts : (Type.t list))), _, (t : (Type.t))) = _menhir_stack in
                let _v : (Type.t list) = 
# 180 "trio/parser.mly"
                                           ( t :: ts )
# 1003 "trio/parser.ml"
                 in
                _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
            | MenhirState41 | MenhirState36 | MenhirState22 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
                let _v : (Type.t list) = 
# 177 "trio/parser.mly"
                ( [t] )
# 1013 "trio/parser.ml"
                 in
                _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
            | MenhirState133 | MenhirState119 | MenhirState13 | MenhirState39 | MenhirState18 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | STAR ->
                    _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
                | ARR ->
                    _menhir_reduce67 _menhir_env (Obj.magic _menhir_stack)
                | EOF | LET | PIPE | RPAREN | SATISFYING | SYNTH | TYPE ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
                    let _v : (Type.t) = 
# 134 "trio/parser.mly"
                  ( t )
# 1031 "trio/parser.ml"
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
                    _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
                | EOF | LET | PIPE | RPAREN | SATISFYING | SYNTH | TYPE ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
                    let _v : (Type.t) = 
# 154 "trio/parser.mly"
                  ( t )
# 1053 "trio/parser.ml"
                     in
                    _menhir_goto_typ_non_variant _menhir_env _menhir_stack _menhir_s _v
                | ARR ->
                    _menhir_reduce67 _menhir_env (Obj.magic _menhir_stack)
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
# 21 "trio/parser.mly"
       (string)
# 1084 "trio/parser.ml"
            ))), _, (t : (Type.t))) = _menhir_stack in
            let _v : (Expr.param) = 
# 214 "trio/parser.mly"
    ( (x, t) )
# 1089 "trio/parser.ml"
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
                        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState56
                    | FUN ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState56
                    | INT _v ->
                        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
                    | LID _v ->
                        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
                    | LPAREN ->
                        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState56
                    | MATCH ->
                        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState56
                    | UID _v ->
                        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState56)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | MenhirState57 ->
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
                        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState59
                    | FUN ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState59
                    | INT _v ->
                        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
                    | LID _v ->
                        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
                    | LPAREN ->
                        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState59
                    | MATCH ->
                        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState59
                    | UID _v ->
                        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59)
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
    | MenhirState119 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), (i : (
# 21 "trio/parser.mly"
       (string)
# 1175 "trio/parser.ml"
        ))), _, (t : (Type.t))) = _menhir_stack in
        let _v : (Expr.declaration) = 
# 126 "trio/parser.mly"
    ( TypeDeclaration (i, t) )
# 1180 "trio/parser.ml"
         in
        _menhir_goto_decl _menhir_env _menhir_stack _menhir_s _v
    | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SATISFYING ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LBRACKET ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState135
            | EOF ->
                _menhir_reduce13 _menhir_env (Obj.magic _menhir_stack) MenhirState135
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState135)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce66 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
    let _v : (Type.t) = 
# 162 "trio/parser.mly"
                ( t )
# 1216 "trio/parser.ml"
     in
    _menhir_goto_typ_non_arrow _menhir_env _menhir_stack _menhir_s _v

and _menhir_run41 : _menhir_env -> 'ttv_tail * _menhir_state * (Type.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LID _v ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v
    | LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState41
    | UNIT ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState41
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState41

and _menhir_goto_typ_tuple_list_one : _menhir_env -> 'ttv_tail -> _menhir_state -> (Type.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | ARR | EOF | LET | PIPE | RPAREN | SATISFYING | SYNTH | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (t : (Type.t))), _, (ts : (Type.t list))) = _menhir_stack in
            let _v : (Type.t list) = 
# 173 "trio/parser.mly"
                                           ( t :: List.rev ts )
# 1253 "trio/parser.ml"
             in
            _menhir_goto_typ_tuple_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | ARR | EOF | LET | PIPE | RPAREN | SATISFYING | SYNTH | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (t : (Type.t))), _, (ts : (Type.t list))) = _menhir_stack in
            let _v : (Type.t list) = 
# 172 "trio/parser.mly"
                                           ( t :: List.rev ts )
# 1275 "trio/parser.ml"
             in
            _menhir_goto_typ_tuple_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState41 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | ARR | EOF | LET | PIPE | RPAREN | SATISFYING | SYNTH | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (t : (Type.t))), _, (ts : (Type.t list))) = _menhir_stack in
            let _v : (Type.t list) = 
# 171 "trio/parser.mly"
                                           ( t :: List.rev ts )
# 1297 "trio/parser.ml"
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

and _menhir_goto_decl_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Expr.declaration list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ds : (Expr.declaration list)) = _v in
        let (_menhir_stack, _menhir_s, (is : (string list))) = _menhir_stack in
        let _v : (string list * Expr.declaration list) = 
# 79 "trio/parser.mly"
      ( (is,ds) )
# 1320 "trio/parser.ml"
         in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState109 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | EOF ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (ids : (string list * Expr.declaration list))) = _menhir_stack in
                let _v : (string list * Expr.declaration list) = 
# 75 "trio/parser.mly"
      ( ids )
# 1336 "trio/parser.ml"
                 in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_1 : (string list * Expr.declaration list)) = _v in
                Obj.magic _1
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState130 ->
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
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v
                | LPAREN ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState133
                | PIPE ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState133
                | UNIT ->
                    _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState133
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState133)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            _menhir_fail ())
    | MenhirState128 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (ds : (Expr.declaration list)) = _v in
        let (_menhir_stack, _menhir_s, (d : (Expr.declaration))) = _menhir_stack in
        let _v : (Expr.declaration list) = 
# 122 "trio/parser.mly"
    ( d::ds )
# 1386 "trio/parser.ml"
         in
        _menhir_goto_decl_list _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_exp_app_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (Expr.t list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
    | COMMA | DOT | EOF | FATEQ | NEQ | PIPE | RBRACKET | RPAREN | SEMI | WITH ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e : (Expr.t))), _, (es : (Expr.t list))) = _menhir_stack in
        let _v : (Expr.t) = 
# 202 "trio/parser.mly"
    ( appify e (List.rev es) )
# 1419 "trio/parser.ml"
         in
        _menhir_goto_exp_app _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState70

and _menhir_goto_exp_app : _menhir_env -> 'ttv_tail -> _menhir_state -> (Expr.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (e : (Expr.t)) = _v in
    let _v : (Expr.t) = 
# 198 "trio/parser.mly"
    ( e )
# 1435 "trio/parser.ml"
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
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState75
            | FUN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState75
            | INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
            | LID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
            | LPAREN ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState75
            | MATCH ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState75
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Expr.t))) = _menhir_stack in
            let _v : (Expr.t) = 
# 256 "trio/parser.mly"
    ( e )
# 1475 "trio/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (es : (Expr.t list))), _, (e : (Expr.t))) = _menhir_stack in
        let _v : (Expr.t list) = 
# 264 "trio/parser.mly"
    ( e :: es )
# 1491 "trio/parser.ml"
         in
        _menhir_goto_exp_comma_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState104 | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (e : (Expr.t))) = _menhir_stack in
        let _v : (Expr.t list) = 
# 262 "trio/parser.mly"
    ( [e] )
# 1501 "trio/parser.ml"
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
            let _v : ((Expr.Pattern.t * Expr.t) list) = 
# 269 "trio/parser.mly"
    ( [] )
# 1516 "trio/parser.ml"
             in
            _menhir_goto_branches _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, (p : (Expr.Pattern.t))), _, (e : (Expr.t))) = _menhir_stack in
        let _v : (Expr.Pattern.t * Expr.t) = 
# 275 "trio/parser.mly"
    ( (p, e) )
# 1532 "trio/parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (b : (Expr.Pattern.t * Expr.t)) = _v in
        let (_menhir_stack, (bs : ((Expr.Pattern.t * Expr.t) list))) = _menhir_stack in
        let _v : ((Expr.Pattern.t * Expr.t) list) = 
# 271 "trio/parser.mly"
    ( b::bs )
# 1541 "trio/parser.ml"
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
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | FUN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _v
            | LID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _v
            | LPAREN ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | MATCH ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState104)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (c : (
# 22 "trio/parser.mly"
       (string)
# 1579 "trio/parser.ml"
            ))), _, (e : (Expr.t))) = _menhir_stack in
            let _v : (Expr.t) = 
# 236 "trio/parser.mly"
    ( mk_unctor_or_ctor_by_name c e )
# 1584 "trio/parser.ml"
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
        let (_menhir_stack, _menhir_s, (_1 : (Expr.t))) = _menhir_stack in
        Obj.magic _1
    | MenhirState123 ->
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
# 21 "trio/parser.mly"
       (string)
# 1615 "trio/parser.ml"
                ))), _, (e : (Expr.t))) = _menhir_stack in
                let _v : (Expr.declaration) = 
# 128 "trio/parser.mly"
    ( ExprDeclaration (i, e) )
# 1620 "trio/parser.ml"
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
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (es : (Expr.t list))), _, (e : (Expr.t))) = _menhir_stack in
        let _v : (Expr.t list * Expr.t) = 
# 103 "trio/parser.mly"
    ( (es,e) )
# 1642 "trio/parser.ml"
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
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | EOF ->
                _menhir_reduce13 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState150)
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (ex : (Expr.t list * Expr.t))) = _menhir_stack in
            let _v : ((Expr.t list * Expr.t) list) = 
# 99 "trio/parser.mly"
    ( [ex] )
# 1668 "trio/parser.ml"
             in
            _menhir_goto_nonempty_examples _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState143 | MenhirState136 ->
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
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState143
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
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143)
        | RBRACKET ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Expr.t))) = _menhir_stack in
            let _v : (Expr.t list) = 
# 114 "trio/parser.mly"
    ( [e] )
# 1713 "trio/parser.ml"
             in
            _menhir_goto_nonempty_exp_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run61 : _menhir_env -> 'ttv_tail * _menhir_state * (Expr.t) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState61
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState61
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState61
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState61
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState61

and _menhir_run63 : _menhir_env -> 'ttv_tail * _menhir_state * (Expr.t) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIX ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState63
    | FUN ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState63
    | INT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v
    | LID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v
    | LPAREN ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState63
    | MATCH ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState63
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63

and _menhir_run65 : _menhir_env -> 'ttv_tail * _menhir_state * (Expr.t) -> _menhir_state -> 'ttv_return =
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
# 26 "trio/parser.mly"
       (int)
# 1788 "trio/parser.ml"
        )) = _v in
        let ((_menhir_stack, _menhir_s, (e : (Expr.t))), _) = _menhir_stack in
        let _v : (Expr.t) = 
# 250 "trio/parser.mly"
    ( Expr.Proj (n, e) )
# 1794 "trio/parser.ml"
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
# 190 "trio/parser.mly"
         ( Type.Tuple [] )
# 1811 "trio/parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState133 | MenhirState119 | MenhirState13 | MenhirState39 | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack)
        | ARR ->
            _menhir_reduce68 _menhir_env (Obj.magic _menhir_stack)
        | EOF | LET | PIPE | RPAREN | SATISFYING | SYNTH | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 135 "trio/parser.mly"
                  ( t )
# 1830 "trio/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState41 | MenhirState36 | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
        let _v : (Type.t list) = 
# 178 "trio/parser.mly"
                ( [t] )
# 1846 "trio/parser.ml"
         in
        _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (ts : (Type.t list))), _, (t : (Type.t))) = _menhir_stack in
        let _v : (Type.t list) = 
# 181 "trio/parser.mly"
                                           ( t :: ts )
# 1856 "trio/parser.ml"
         in
        _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack)
        | EOF | LET | PIPE | RPAREN | SATISFYING | SYNTH | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 155 "trio/parser.mly"
                  ( t )
# 1872 "trio/parser.ml"
             in
            _menhir_goto_typ_non_variant _menhir_env _menhir_stack _menhir_s _v
        | ARR ->
            _menhir_reduce68 _menhir_env (Obj.magic _menhir_stack)
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
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
            | LPAREN ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState17
            | UNIT ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState17
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17)
        | EOF | LET | PIPE | RPAREN | SATISFYING | SYNTH | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), (i : (
# 22 "trio/parser.mly"
       (string)
# 1918 "trio/parser.ml"
            ))) = _menhir_stack in
            let _v : (string * Type.t) = 
# 148 "trio/parser.mly"
    ( (i, (Tuple [])) )
# 1923 "trio/parser.ml"
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
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | PIPE ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | UNIT ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18

and _menhir_run19 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 21 "trio/parser.mly"
       (string)
# 1961 "trio/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (d : (
# 21 "trio/parser.mly"
       (string)
# 1969 "trio/parser.ml"
    )) = _v in
    let _v : (Type.t) = 
# 184 "trio/parser.mly"
          ( Type.Named (d) )
# 1974 "trio/parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (ts : (Type.t list))), _, (t : (Type.t))) = _menhir_stack in
        let _v : (Type.t list) = 
# 179 "trio/parser.mly"
                                           ( t :: ts )
# 1985 "trio/parser.ml"
         in
        _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState41 | MenhirState36 | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
        let _v : (Type.t list) = 
# 176 "trio/parser.mly"
                ( [t] )
# 1995 "trio/parser.ml"
         in
        _menhir_goto_typ_tuple_list_one _menhir_env _menhir_stack _menhir_s _v
    | MenhirState133 | MenhirState119 | MenhirState13 | MenhirState18 | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | STAR ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack)
        | ARR ->
            _menhir_reduce66 _menhir_env (Obj.magic _menhir_stack)
        | EOF | LET | PIPE | RPAREN | SATISFYING | SYNTH | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 133 "trio/parser.mly"
                  ( t )
# 2013 "trio/parser.ml"
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
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack)
        | EOF | LET | PIPE | RPAREN | SATISFYING | SYNTH | TYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Type.t))) = _menhir_stack in
            let _v : (Type.t) = 
# 153 "trio/parser.mly"
                  ( t )
# 2035 "trio/parser.ml"
             in
            _menhir_goto_typ_non_variant _menhir_env _menhir_stack _menhir_s _v
        | ARR ->
            _menhir_reduce66 _menhir_env (Obj.magic _menhir_stack)
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
    let _v : (Expr.declaration list) = 
# 120 "trio/parser.mly"
    ( [] )
# 2059 "trio/parser.ml"
     in
    _menhir_goto_decl_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_run117 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState119 _v
            | LPAREN ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | PIPE ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | UNIT ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState119)
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

and _menhir_run121 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState123
            | FUN ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState123
            | INT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
            | LID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
            | LPAREN ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState123
            | MATCH ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState123
            | UID _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState123)
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

and _menhir_goto_exp_base : _menhir_env -> 'ttv_tail -> _menhir_state -> (Expr.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | FATEQ ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | NEQ ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | COMMA | EOF | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | PIPE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (a : (Expr.param))), _, (e : (Expr.t))) = _menhir_stack in
            let _v : (Expr.t) = 
# 228 "trio/parser.mly"
    ( Expr.Fix ((fst a), (snd a), e) )
# 2174 "trio/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState60)
    | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | FATEQ ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | NEQ ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | COMMA | EOF | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | PIPE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Expr.t))), _), _, (e2 : (Expr.t))) = _menhir_stack in
            let _v : (Expr.t) = 
# 254 "trio/parser.mly"
    ( Expr.Eq (false, e1, e2) )
# 2198 "trio/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62)
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | FATEQ ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | NEQ ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | COMMA | EOF | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | PIPE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (e1 : (Expr.t))), _), _, (e2 : (Expr.t))) = _menhir_stack in
            let _v : (Expr.t) = 
# 252 "trio/parser.mly"
    ( Expr.Eq (true, e1, e2) )
# 2222 "trio/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState64)
    | MenhirState56 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | FATEQ ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | NEQ ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState67
        | COMMA | EOF | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | PIPE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (x : (Expr.param))), _, (e : (Expr.t))) = _menhir_stack in
            let _v : (Expr.t) = 
# 226 "trio/parser.mly"
    ( Expr.Func (x, e) )
# 2246 "trio/parser.ml"
             in
            _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState67)
    | MenhirState143 | MenhirState136 | MenhirState140 | MenhirState123 | MenhirState0 | MenhirState104 | MenhirState3 | MenhirState99 | MenhirState5 | MenhirState75 | MenhirState78 | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | FATEQ ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | FIX ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | FUN ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | INT _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
        | LID _v ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
        | LPAREN ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | MATCH ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | NEQ ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | UID _v ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
        | COMMA | EOF | PIPE | RBRACKET | RPAREN | SEMI | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Expr.t))) = _menhir_stack in
            let _v : (Expr.t) = 
# 204 "trio/parser.mly"
    ( e )
# 2284 "trio/parser.ml"
             in
            _menhir_goto_exp_app _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState68)
    | MenhirState68 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState69
        | FATEQ ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState69
        | NEQ ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState69
        | COMMA | EOF | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | PIPE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Expr.t))) = _menhir_stack in
            let _v : (Expr.t list) = 
# 208 "trio/parser.mly"
    ( [e] )
# 2308 "trio/parser.ml"
             in
            _menhir_goto_exp_app_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState69)
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState71
        | FATEQ ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState71
        | NEQ ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState71
        | COMMA | EOF | FIX | FUN | INT _ | LID _ | LPAREN | MATCH | PIPE | RBRACKET | RPAREN | SEMI | UID _ | WITH ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (es : (Expr.t list))), _, (e : (Expr.t))) = _menhir_stack in
            let _v : (Expr.t list) = 
# 210 "trio/parser.mly"
    ( e::es )
# 2332 "trio/parser.ml"
             in
            _menhir_goto_exp_app_list _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71)
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
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
            | LPAREN ->
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
    | MenhirState111 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), (s : (
# 23 "trio/parser.mly"
       (string)
# 2394 "trio/parser.ml"
        ))), _, (is : (string list))) = _menhir_stack in
        let _v : (string list) = 
# 83 "trio/parser.mly"
      ( s::is )
# 2399 "trio/parser.ml"
         in
        _menhir_goto_imports _menhir_env _menhir_stack _menhir_s _v
    | MenhirState130 | MenhirState109 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LET ->
            _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState116
        | TYPE ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState116
        | EOF | SYNTH ->
            _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) MenhirState116
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116)
    | _ ->
        _menhir_fail ()

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 22 "trio/parser.mly"
       (string)
# 2423 "trio/parser.ml"
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
# 21 "trio/parser.mly"
       (string)
# 2437 "trio/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s, (c : (
# 22 "trio/parser.mly"
       (string)
# 2442 "trio/parser.ml"
        ))) = _menhir_stack in
        let _v : (Expr.t) = 
# 240 "trio/parser.mly"
    ( mk_unctor_or_ctor_by_name c (Expr.Var x) )
# 2447 "trio/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FIX ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState3
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
# 22 "trio/parser.mly"
       (string)
# 2475 "trio/parser.ml"
            ))) = _menhir_stack in
            let _v : (Expr.t) = 
# 242 "trio/parser.mly"
    ( mk_unctor_or_ctor_by_name c unit_ )
# 2480 "trio/parser.ml"
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
# 22 "trio/parser.mly"
       (string)
# 2496 "trio/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s, (c1 : (
# 22 "trio/parser.mly"
       (string)
# 2501 "trio/parser.ml"
        ))) = _menhir_stack in
        let _v : (Expr.t) = 
# 238 "trio/parser.mly"
    ( mk_unctor_or_ctor_by_name c1 (mk_unctor_or_ctor_by_name c2 unit_) )
# 2506 "trio/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | COMMA | DOT | EOF | FATEQ | FIX | FUN | INT _ | MATCH | NEQ | PIPE | RBRACKET | RPAREN | SEMI | WITH ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (c : (
# 22 "trio/parser.mly"
       (string)
# 2514 "trio/parser.ml"
        ))) = _menhir_stack in
        let _v : (Expr.t) = 
# 232 "trio/parser.mly"
    (
      mk_unctor_or_ctor_by_name c unit_
    )
# 2521 "trio/parser.ml"
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
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState5
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
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState6
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
        let _v : (Expr.t) = 
# 258 "trio/parser.mly"
    ( unit_ )
# 2583 "trio/parser.ml"
         in
        _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v
    | UID _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 21 "trio/parser.mly"
       (string)
# 2596 "trio/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (x : (
# 21 "trio/parser.mly"
       (string)
# 2604 "trio/parser.ml"
    )) = _v in
    let _v : (Expr.t) = 
# 224 "trio/parser.mly"
    ( Expr.Var x )
# 2609 "trio/parser.ml"
     in
    _menhir_goto_exp_base _menhir_env _menhir_stack _menhir_s _v

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 26 "trio/parser.mly"
       (int)
# 2616 "trio/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (c : (
# 26 "trio/parser.mly"
       (int)
# 2624 "trio/parser.ml"
    )) = _v in
    let _v : (Expr.t) = 
# 230 "trio/parser.mly"
    ( Expr.from_int c )
# 2629 "trio/parser.ml"
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

and _menhir_run57 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState57
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState57

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState136 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState135 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState128 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState123 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState119 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState111 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState109 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState104 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState94 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState87 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState86 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState68 ->
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
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState60 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState56 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState41 ->
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
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
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
# 84 "trio/parser.mly"
      ( [] )
# 2860 "trio/parser.ml"
     in
    _menhir_goto_imports _menhir_env _menhir_stack _menhir_s _v

and _menhir_run110 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
            _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState111
        | EOF | LET | SYNTH | TYPE ->
            _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState111
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState111)
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

and exp : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Expr.t) =
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
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState0
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

and imports_decls_start : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (string list * Expr.declaration list) =
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
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState109
    | EOF | LET | TYPE ->
        _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState109
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState109)

and unprocessed_problem : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Specification.t_unprocessed) =
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
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | LET | SYNTH | TYPE ->
        _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState130
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState130)

# 269 "<standard.mly>"
  

# 2979 "trio/parser.ml"
