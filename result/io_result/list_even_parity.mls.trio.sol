fix (f : list -> bool) =
  fun (x:list) ->
    match x with
      | Nil _ -> True
      | Cons _ -> (match Un_Cons x . 0 with
                     | False _ -> f (Un_Cons x . 1)
                     | True _ -> bnot (f (Un_Cons x . 1)))