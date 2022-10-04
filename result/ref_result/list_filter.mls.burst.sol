fix (f : (nat -> bool) * list -> list) =
  fun (x:(nat -> bool) * list) ->
    match x . 1 with
      | Nil _ -> x . 1
      | Cons _ -> (match x . 0 (Un_Cons (x . 1) . 0) with
                     | True _ -> Cons (Un_Cons (x . 1) . 0,
                                        f (x . 0, Un_Cons (x . 1) . 1))
                     | False _ -> f (x . 0, Un_Cons (x . 1) . 1))