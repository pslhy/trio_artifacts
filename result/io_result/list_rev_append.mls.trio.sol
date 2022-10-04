fix (f : list -> list) =
  fun (x:list) ->
    match x with
      | Nil _ -> x
      | Cons _ -> (match Un_Cons x . 1 with
                     | Nil _ -> x
                     | Cons _ -> append (f (Un_Cons (Un_Cons x . 1) . 1))
                                   Cons (Un_Cons x . 0, Cons (0, Nil)))