open MyStdLib
open Burst
open Lang

(* Burst -> Trio *)
let rec convert_type_to_trio
    (t: Burst.Type.t)
  : Trio.Type.t =
  match Burst.Type.node t with
  | Named v -> Trio.Type.Named (Id.to_string v)
  | Arrow (t1,t2) -> Trio.Type.Arrow (convert_type_to_trio t1, convert_type_to_trio t2)
  | Tuple ts -> let trio_ts = 
                  List.map ~f:(fun t -> convert_type_to_trio t) ts in 
                  Trio.Type.Tuple trio_ts
  (* Mu ? *)
  | Mu (i,t) -> convert_type_to_trio t
  | Variant branches -> 
          let (ss,ts) = Trio.Vocab.list_unzip branches in
          let trio_ss = List.map ~f:(fun i -> Id.to_string i) ss in
          let trio_ts = List.map ~f:(fun t -> convert_type_to_trio t) ts in
          Trio.Type.Variant (Trio.Vocab.list_combine trio_ss trio_ts)
          (* List.map ~f:(fun (bi,bt) -> 
            Trio.Type.Variant (Id.to_string bi, convert_type_to_trio bt) 
          ) branches *)

let rec convert_pattern_to_trio
    (p: Burst.Lang.Pattern.t)
  : Trio.Expr.Pattern.t =
  match p with
  | Tuple ps -> Trio.Expr.Pattern.Tuple (List.map ~f:convert_pattern_to_trio ps)
  | Ctor (i,p') -> Trio.Expr.Pattern.Ctor (Id.to_string i, convert_pattern_to_trio p')
  | Var i -> Trio.Expr.Pattern.Var (Id.to_string i)
  | Wildcard -> Trio.Expr.Pattern.Wildcard

let rec convert_exp_to_trio
    (e: Burst.Lang.Expr.t)
  : Trio.Expr.t =
  match Burst.Lang.Expr.node e with
  | Var i -> Trio.Expr.Var (Id.to_string i)
  | Wildcard -> Trio.Expr.Wildcard
  | App (e1,e2) -> Trio.Expr.App (convert_exp_to_trio e1, convert_exp_to_trio e2)
  | Func ((i,t),e) -> let s = Id.to_string i in
                      let t_t = convert_type_to_trio t in
                      let t_e = convert_exp_to_trio e in
                      Trio.Expr.Func ((s,t_t),t_e)
  | Ctor (i,e) -> Trio.Expr.Ctor (Id.to_string i, convert_exp_to_trio e)
  | Match (e,branches) -> 
        let t_e = convert_exp_to_trio e in
        let t_branches = List.map ~f:(fun (p,e) ->
                                      let trio_p = convert_pattern_to_trio p in
                                      let trio_e = convert_exp_to_trio e in
                                      (trio_p, trio_e)
                                      ) branches
        in
        Trio.Expr.Match (t_e, t_branches)
  | Fix (i,t,e) -> Trio.Expr.Fix (Id.to_string i, convert_type_to_trio t, convert_exp_to_trio e)
  | Tuple es -> Trio.Expr.Tuple (List.map ~f:convert_exp_to_trio es)
  | Proj (num,e) -> Trio.Expr.Proj (num, convert_exp_to_trio e)
  | _ -> failwith "convert_exp_to_trio invalid"

let convert_unprocessed_spec_to_trio 
    (unspec: Burst.Problem.unprocessed_spec)
  : Trio.Specification.unprocessed_spec = 
      match unspec with
      | UIOEs us -> 
        let examples = List.map ~f:(fun (es,e) -> 
          let trio_es = List.map ~f:convert_exp_to_trio es in
          let trio_e = convert_exp_to_trio e in
          (trio_es, trio_e)
          ) us
        in 
        Trio.Specification.UIOEs examples
      | UEquiv us ->
        let examples = [] in
        Trio.Specification.UIOEs examples
      | _ -> failwith ("convert io to trio")

let convert_decl_list_to_trio
    (ds: Declaration.t list)
  : Trio.Expr.declaration list =
  let trio_ds = List.map ~f:(fun d -> let trio_d =
                                      match d with 
                                      | TypeDeclaration (i,t) -> Trio.Expr.TypeDeclaration (Id.to_string i, convert_type_to_trio t)
                                      | ExprDeclaration (i,e) -> Trio.Expr.ExprDeclaration (Id.to_string i, convert_exp_to_trio e)
                                   in
                                   trio_d
                          ) ds
  in
  trio_ds

let rec convert_value_to_trio (v: Burst.Lang.Value.t)
  : Trio.Expr.value = 
  match Burst.Lang.Value.node v with
  | Func ((i,t), e) -> Trio.Expr.FuncV ((Id.to_string i, convert_type_to_trio t), convert_exp_to_trio e)
  | Ctor (i, v) -> Trio.Expr.CtorV (Id.to_string i, convert_value_to_trio v)
  | Tuple vs -> Trio.Expr.TupleV (List.map ~f:convert_value_to_trio vs)
  | Wildcard -> Trio.Expr.WildcardV

(* Trio -> Burst *)
let rec convert_type_to_burst (t: Trio.Type.t): Burst.Type.t =
  match t with
  | Trio.Type.Named s -> Type.mk_named (Id.create s)
  | Trio.Type.Arrow (t1,t2) -> Type.mk_arrow (convert_type_to_burst t1) (convert_type_to_burst t2)
  | Trio.Type.Tuple ts -> Type.mk_tuple (List.map ~f:convert_type_to_burst ts)
  | Trio.Type.Variant branches -> Type.mk_variant (List.map ~f:(fun (s,t) -> (Id.create s, convert_type_to_burst t)) branches)

let rec convert_pattern_to_burst (p: Trio.Expr.Pattern.t): Burst.Lang.Pattern.t =
  match p with
  | Trio.Expr.Pattern.Tuple ps -> Pattern.Tuple (List.map ~f:convert_pattern_to_burst ps)
  | Trio.Expr.Pattern.Ctor (s,t) -> Pattern.Ctor ((Id.create s), convert_pattern_to_burst t)
  | Trio.Expr.Pattern.Var s -> Pattern.Var (Id.create s)
  | Trio.Expr.Pattern.Wildcard -> Pattern.Wildcard

(* counter changes proj ex) x.0 x.1 .. *)
let rec convert_expr_to_burst (e: Trio.Expr.t) : Burst.Lang.Expr.t =
  match e with
  | Trio.Expr.Var id -> Expr.mk_var (Id.create id)
  | Trio.Expr.Wildcard -> Expr.mk_wildcard
  | Trio.Expr.App (e1,e2) -> let b_e1 = (convert_expr_to_burst e1) in
                             let b_e2 = (convert_expr_to_burst e2) in
                             Expr.mk_app b_e1 b_e2
  | Trio.Expr.Func ((s,t), e) -> 
                        let b_t = (convert_type_to_burst t) in
                        let b_e = (convert_expr_to_burst e) in
                        Expr.mk_func (Id.create s, b_t) b_e
  | Trio.Expr.Ctor (s,e) -> let b_e = convert_expr_to_burst e in
                            Expr.mk_ctor (Id.create s) b_e
  | Trio.Expr.Unctor (s,e) -> let b_e = (convert_expr_to_burst e) in
                              Expr.mk_unctor (Id.create s) b_e
  | Trio.Expr.Eq (b,e1,e2) -> let b_e1 = (convert_expr_to_burst e1) in
                              let b_e2 = (convert_expr_to_burst e2) in
                              Expr.mk_eq b b_e1 b_e2
  | Trio.Expr.Match (e,branches) -> 
        let b_e = convert_expr_to_burst e in
        let b_branches = List.map ~f:(fun (p,e) -> 
                                        let b_e' = convert_expr_to_burst e in
                                        let b_p = (convert_pattern_to_burst p) in 
                                        (b_p, b_e')) branches
        in
        Expr.mk_match b_e b_branches
  | Trio.Expr.Fix (i,t,e) -> let b_t= (convert_type_to_burst t) in
                             let b_e = (convert_expr_to_burst e) in
                             Expr.mk_fix (Id.create i) b_t b_e
  | Trio.Expr.Tuple explist -> 
          let es = 
            List.fold_right ~f:(fun e es -> 
                                let e = convert_expr_to_burst e in
                                (e::es))
                            ~init:([])
                            explist
          in
          Expr.mk_tuple es
  | Trio.Expr.Proj (i,e) -> let b_e= (convert_expr_to_burst e) in
                            (Expr.mk_proj (i) b_e)

module T : Burst.Synthesizers.IOSynth.S = struct
  type t = (Context.t * Type.t * Type.t) * Problem.t

  let init
      ~(problem:Problem.t)
      ~(context:Context.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
    : t =
    ((context,tin,tout),problem)

  let context = fst3 % fst
  let tin = snd3 % fst
  let tout = trd3 % fst
  let problem = snd

  let first = ref true 
  let rec term_of_type
      (c:Context.t)
      (t:Type.t)
    : Expr.t =
        begin match Type.node t with
          | Named i -> term_of_type c (Context.find_exn c.tc i)
          | Arrow (t1,t2) ->
            Expr.mk_func
              (Id.create "x",t1)
              (term_of_type c t2)
          | Tuple ts ->
            Expr.mk_tuple (List.map ~f:(term_of_type c) ts)
          | Mu _ -> failwith "TODO"
          | Variant bs ->
            (* let (i,t) = List.hd_exn bs in *)
            (* let _ = prerr_endline (string_of_int (List.length bs)) in  *)

            (* let (i,t) = 
              if !first then List.last_exn bs 
              else List.hd_exn bs
            in *)
            
            (* let _ = prerr_endline (Type.show t) in  *)
            (* let (i,t) = List.random_element_exn bs in *)

            (* let type_compare t1 t2 = 
              match (t1, t2) with 
              Type.Tuple [], _ -> 1
              | _, Type.Tuple [] -> -1 
              | _ -> Stdlib.compare t1 t2
            in
            let bs = 
              List.sort (List.map bs ~f:(fun (i,t) -> (i, Type.node t)))
                 ~compare:(fun (_,t1) (_, t2) -> type_compare t1 t2) 
            in
            let (i,t) = List.hd_exn bs in *)

            let (i,t) = 
              if !first then List.last_exn bs 
              (* List.find_exn bs ~f:(fun (_,t) -> 
                match (Type.node t) with 
                | Type.Tuple [] -> false
                | _ -> true
              ) *)
              else 
              List.hd_exn bs
            in
            let _ = first := false in
            Expr.mk_ctor i (term_of_type c t)
        end

  let synthesize
      (a:t)
      (ios:(Value.t * Value.t) list)
    : Expr.t =
    (* ios preprocess *)
    let trio_ios = List.map ~f:(fun (v1,v2) -> (convert_value_to_trio v1, convert_value_to_trio v2)) ios in
    if (List.length ios = 0) then
      term_of_type (context a) (Type.mk_arrow (tin a) (tout a))
    else
    let ios = List.map ~f:(fun (v1,v2) -> (Value.to_exp v1,Value.to_exp v2)) ios in
    let ios =
      List.map
        ~f:(fun (vin,vout) ->
            begin match Expr.destruct_tuple vin with
              | Some vins -> (vins,vout)
              | None -> ([vin],vout)
            end)
        ios
    in
    let tins =
      begin match Type.destruct_tuple (tin a) with
        | None -> [(tin a)]
        | Some tins -> tins
      end
    in
    let burst_problem = (problem a) in

    let problem_spec = burst_problem.spec in
    (* prerr_endline (Burst.Problem.show_spec problem_spec); *)

    (* make trio.specification.spec  *)
    let (ss, ds, t, dss, unspec) = burst_problem.unprocessed in
    (* prerr_endline ("====unspec====="); *)
    (* prerr_endline (Burst.Problem.show_unprocessed_spec unspec); *)
    let trio_unspec = convert_unprocessed_spec_to_trio unspec in
    (* prerr_endline ("====converted unspec=====");
    prerr_endline (Trio.Specification.show_unprocessed_spec trio_unspec); *)
    let trio_ds = convert_decl_list_to_trio ds in
    let trio_t = convert_type_to_trio t in
    (* converted datas *)
    let unprocessed_spec = (ss, trio_ds, trio_t, trio_unspec) in
    let spec = Trio.Specification.process unprocessed_spec in
    let spec =
      let src_ty, dst_ty = (fst spec.synth_type, snd spec.synth_type) in 
      let tc = spec.tc in 
      let tc = BatMap.add Trio.Expr.target_func (Trio.Type.Arrow(src_ty, dst_ty)) tc in
      let tc = BatMap.add Trio.Expr.target_func_arg src_ty tc in   
      {spec with tc = tc}
    in
    let spec = {spec with spec = trio_ios}
    in
    (* prerr_endline (Trio.Specification.show spec); *)
    (* Trio synthesizer ! *)
    let result = 
      try
        Trio.Bidirectional.synthesis spec
      with Trio.Generator.SolutionFound sol -> 
      Trio.Generator.wrap spec sol
    in
    (* prerr_endline (Trio.Expr.show result); *)
    (* Trio to Burst.. *)
    let convert_result = convert_expr_to_burst result in
    (* prerr_endline ("convert_result");
    prerr_endline (Burst.Lang.Expr.show convert_result); *)
    convert_result

  
  let synth
      (a:t)
      (ios:(Value.t * Value.t) list)
    : t * Expr.t =
    (a,synthesize a ios)
end