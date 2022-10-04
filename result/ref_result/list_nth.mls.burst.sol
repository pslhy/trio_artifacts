fix (f : list * nat -> nat) =
  fun (x:list * nat) ->
    match x . 0 with
      | Nil _ -> 0
      | Cons _ -> (match x . 1 with
                     | O _ -> Un_Cons (x . 0) . 0
                     | S _ -> f (Un_Cons (x . 0) . 1, Un_S (x . 1)))