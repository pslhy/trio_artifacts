fix (f : (nat -> bool) * list -> list) =
  fun (x:(nat -> bool) * list) ->
    match x . 1 with
      | Nil _ -> x . 1
      | Cons _ -> (match x . 0 S (Un_Cons (x . 1) . 0) with
                     | False _ -> x . 1
                     | True _ -> (match Un_Cons (x . 1) . 0 with
                                    | O _ -> Un_Cons (x . 1) . 1
                                    | S _ -> Cons (0, Nil)))