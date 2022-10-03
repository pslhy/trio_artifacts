fix (f : nat * nat -> nat) =
  fun (x:nat * nat) ->
    match x . 1 with
      | O _ -> x . 1
      | S _ -> add (f (Un_S (x . 1), x . 0)) (x . 0)