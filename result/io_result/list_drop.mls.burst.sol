fix (f : list * nat -> list) =
  fun (x:list * nat) ->
    match x . 1 with
      | O _ -> x . 0
      | S _ -> Un_Cons (f (x . 0, Un_S (x . 1))) . 1