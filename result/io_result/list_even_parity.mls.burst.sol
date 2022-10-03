fix (f : list -> bool) =
  fun (x:list) ->
    match x with
      | Nil _ -> True
      | Cons _ -> (match f (Un_Cons x . 1) with
                     | True _ -> bnot (Un_Cons x . 0)
                     | False _ -> Un_Cons x . 0)