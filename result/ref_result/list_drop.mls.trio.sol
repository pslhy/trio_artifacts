fix (f : list * nat -> list) =
  fun (x:list * nat) ->
    match x . 0 with
      | Nil _ -> x . 0
      | Cons _ -> (match x . 1 with
                     | O _ -> x . 0
                     | S _ -> f (Un_Cons (x . 0) . 1, Un_S (x . 1)))