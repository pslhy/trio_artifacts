fix (f : list -> natopt) =
  fun (x:list) ->
    match x with
      | Nil _ -> None
      | Cons _ -> (match Un_Cons x . 1 with
                     | Nil _ -> Some (Un_Cons x . 0)
                     | Cons _ -> f (Un_Cons x . 1))