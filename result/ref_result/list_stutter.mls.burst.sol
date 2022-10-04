fix (f : list -> list) =
  fun (x:list) ->
    match x with
      | Nil _ -> x
      | Cons _ -> Cons (Un_Cons x . 0,
                         Cons (Un_Cons x . 0, f (Un_Cons x . 1)))