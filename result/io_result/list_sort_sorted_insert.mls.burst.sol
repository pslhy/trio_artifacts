fix (f : list -> list) =
  fun (x:list) ->
    match x with
      | Nil _ -> x
      | Cons _ -> insert (f (Un_Cons x . 1)) (Un_Cons x . 0)