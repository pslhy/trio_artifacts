fix (f : list -> list) =
  fun (x:list) ->
    match x with
      | Nil _ -> x
      | Cons _ -> (match Un_Cons x . 1 with
                     | Nil _ -> x
                     | Cons _ -> (match compare (Un_Cons (Un_Cons x . 1) . 0)
                                          (Un_Cons x . 0) with
                                    | EQ _ -> f (Un_Cons x . 1)
                                    | GT _ -> Cons (Un_Cons x . 0,
                                                     f (Un_Cons x . 1))
                                    | LT _ -> Cons (Un_Cons x . 0,
                                                     f (Un_Cons x . 1))))