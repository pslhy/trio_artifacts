open MyStdLib
open Lang

module T = struct
  (* let ios_sofar : (Value.t * Value.t) list ref = ref [] *)
  let init_ios : (Value.t * Value.t) list ref = ref []  
  let cexs : Value.t list ref = ref [] 
  let _NUM_CHECKS_ = 4096
  let _MAX_SIZE_ = 32

  let num_nothing = ref 0

  module TypeToGeneratorDict =
  struct
    module Generators =
    struct
      type t = Expr.t Sequence.t
      [@@deriving ord]

      let hash _ = failwith "dont"
      let hash_fold_t _ = failwith "don't"
      let pp _ = failwith "don't"
      let equal _ _ = failwith "don't"
      let show _ = failwith "don't"
    end
    module D = DictOf(Type)(Generators)

    type t = D.t * (Type.t -> Expr.t Sequence.t)

    (*let get_val
        ((d,fs):t)
        (t:Type.t)
      : t * Expr.t =
      begin match D.lookup d t with
        | None ->
          let g = fs t in
          let (v,g) = Option.value_exn (Sequence.next g) in
          let d = D.insert d t g in
          ((d,fs),v)
        | Some g ->
          let (v,g) = Option.value_exn (Sequence.next g) in
          let d = D.insert d t g in
          ((d,fs),v)
      end*)

    let create
        (fs:(Type.t -> Expr.t Sequence.t))
      : t =
      (D.empty,fs)
  end

  let rec elements_of_type_and_size_internal
      (context:Context.t)
      (tc:Context.Types.t)
      (t:Type.t)
      (s:int)
    : Value.t list =
    let elements_simple = elements_of_type_and_size_internal context tc in
    if s <= 0 then
      []
    else
      begin match Type.node t with
        | Named i ->
          elements_simple (Context.find_exn tc i) s
        | Arrow _ ->
          let ids = List.filter (Map.to_alist context.full_ec) (fun (i,t') -> Typecheck.type_equiv context.full_tc t t') in
          let vs = List.map ~f:(fun (i,_) -> Eval.evaluate_with_holes ~eval_context:context.full_evals (List.Assoc.find_exn context.full_evals ~equal:Id.equal i)) ids in
          if s = 1 then vs else []
        | Tuple ts ->
          if (List.length ts) = 0 && s <> 1 then
            []
          else
            let parts = partitions (s-1) (List.length ts) in
            let components =
              List.concat_map
                ~f:(fun part ->
                    let components =
                      List.map2_exn
                        ~f:(fun t p -> elements_simple t p)
                        ts
                        part
                    in
                    combinations components)
                parts
            in
            List.map ~f:Value.mk_tuple components
        | Mu (v,t) ->
          let tc = Context.set tc ~key:v ~data:t in
          elements_of_type_and_size_internal context tc t s
        | Variant options ->
          List.concat_map
            ~f:(fun (i,t) ->
                List.map
                  ~f:(Value.mk_ctor i)
                  (elements_simple t (s-1)))
            options
      end

  let elements_of_type_and_size
      (context:Context.t)
      (t:Type.t)
      (s:int)
    : Value.t list =
    let res = elements_of_type_and_size_internal context context.tc t s in
    if List.length res = 0 then num_nothing := !num_nothing+1;
    res

  let sequence_of_type
      (context:Context.t)
      (t:Type.t)
    : Value.t Sequence.t =
    let num_seq =
      Sequence.unfold
        ~init:0
        ~f:(fun i ->
            if !num_nothing < 200 && _MAX_SIZE_ > i then
              Some (i,i+1)
            else
              None)
    in
    Sequence.concat_map ~f:(Sequence.of_list % elements_of_type_and_size context t) num_seq

  let satisfies_post
      ~(context:Context.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(cand:Expr.t)
      ~(checker:Value.t -> Value.t -> bool)
    : Value.t option =
    num_nothing := 0;
    let generator = sequence_of_type context tin in
    let io_seq =
      Sequence.map
        ~f:(fun v ->
            (v,Eval.safe_evaluate_with_holes ~eval_context:context.evals (Expr.mk_app cand (Value.to_exp v))))
        generator
    in
    let io_finite =
      Sequence.take
        io_seq
        _NUM_CHECKS_
    in
    Sequence.find_map
    ~f:(fun (i,o) ->
      begin match o with
        | Some o ->
          if checker i o then
            None
          else
            Some i
        | None ->
          Some i
      end) 
    io_finite 
    (* let beam_size = 2 in 
    let new_cexs = ref [] in
    for i = 1 to beam_size do
      new_cexs := 
      Sequence.filter_map
        ~f:(fun (i,o) ->
            begin match o with
              | Some o ->
                if checker i o then
                  None
                else
                  Some i
              | None ->
                Some i
            end) 
        io_finite 
        |> (fun seq -> Sequence.take seq beam_size) 
        |> Sequence.to_list 
        |> (fun x -> x @ !new_cexs)
    done;
    if List.is_empty !new_cexs then None 
    else 
      let _ = cexs := !new_cexs in
      Some (List.hd_exn !new_cexs) *)
    (* try
      List.find_exn !cex_opts ~f:(fun i -> 
        List.for_all !ios_sofar ~f:(fun (i',_) -> 
            match (Value.node i, Value.node i') with 
            | Tuple is, Tuple is' -> 
              if (List.length is) <> (List.length is') then false 
              else 
                List.exists2_exn is is' ~f:(fun i i' -> 
                  match (Value.node i, Value.node i') with 
                  | Ctor (i, _), Ctor (i', _) -> not (Id.equal i i')
                  | _ -> false
                )
            | Ctor (i, _), Ctor (i', _) -> 
              not (Id.equal i i')
            | _ -> false 
          )
      ) |> (fun x -> Some x )
      (* List.find_exn !cex_opts ~f:(fun cex_opt -> 
        match cex_opt with 
        | None -> false
        | Some i -> List.for_all !ios_sofar ~f:(fun (i',_) -> 
            match (Value.node i, Value.node i') with 
            | Tuple is, Tuple is' -> 
              if (List.length is) <> (List.length is') then false 
              else 
                List.exists2_exn is is' ~f:(fun i i' -> 
                  match (Value.node i, Value.node i') with 
                  | Ctor (i, _), Ctor (i', _) -> not (Id.equal i i')
                  | _ -> false
                )
            | Ctor (i, _), Ctor (i', _) -> 
              not (Id.equal i i')
            | _ -> false 
          )
      ) *)
    with _ -> Some (List.hd_exn !cex_opts) *)
end
