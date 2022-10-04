fix (f : nat * nat -> nat) =
  fun (x:nat * nat) ->
    match x . 1 with
      | O _ -> x . 0
      | S _ -> S (f (x . 0, Un_S (x . 1)))