fix (f : nat * nat -> nat) =
  fun (x:nat * nat) ->
    match x . 0 with
      | O _ -> x . 0
      | S _ -> add (f (Un_S (x . 0), x . 1)) (x . 1)