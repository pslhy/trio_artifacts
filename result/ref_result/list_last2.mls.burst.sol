fix (f : list -> natopt) =
  fun (x:list) ->
    match x with
      | Nil _ -> None
      | Cons _ -> (match Un_Cons x . 1 with
                     | Nil _ -> None
                     | Cons _ -> (match f (Un_Cons x . 1) with
                                    | None _ -> Some (Un_Cons x . 0,
                                                       Un_Cons (Un_Cons x . 1)
                                                         . 0)
                                    | Some _ -> f (Un_Cons x . 1)))