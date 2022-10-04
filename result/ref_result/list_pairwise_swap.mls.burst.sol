fix (f : list -> list) =
  fun (x:list) ->
    match x with
      | Nil _ -> x
      | Cons _ -> (match Un_Cons x . 1 with
                     | Nil _ -> Un_Cons x . 1
                     | Cons _ -> Cons (Un_Cons (Un_Cons x . 1) . 0,
                                        Cons (Un_Cons x . 0,
                                               f
                                                 (Un_Cons (Un_Cons x . 1) . 1))))