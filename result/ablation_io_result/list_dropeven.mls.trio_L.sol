fix (f : list -> list) =
  fun (x:list) ->
    match x with
      | Nil _ -> x
      | Cons _ -> (match is_even (Un_Cons x . 0) with
                     | False _ -> Cons (Un_Cons x . 0, f (Un_Cons x . 1))
                     | True _ -> Un_Cons x . 1)