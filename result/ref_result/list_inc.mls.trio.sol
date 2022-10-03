fix (f : list -> list) =
  fun (x:list) ->
    match x with
      | Nil _ -> x
      | Cons _ -> Cons (S (Un_Cons x . 0), f (Un_Cons x . 1))