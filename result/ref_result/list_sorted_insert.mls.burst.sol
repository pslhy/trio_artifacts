fix (f : list * nat -> list) =
  fun (x:list * nat) ->
    match x . 0 with
      | Nil _ -> Cons (x . 1, x . 0)
      | Cons _ -> (match compare (x . 1) (Un_Cons (x . 0) . 0) with
                     | LT _ -> Cons (x . 1, x . 0)
                     | EQ _ -> x . 0
                     | GT _ -> Cons (Un_Cons (x . 0) . 0,
                                      f (Un_Cons (x . 0) . 1, x . 1)))