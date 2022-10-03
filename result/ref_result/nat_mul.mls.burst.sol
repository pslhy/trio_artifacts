fix (f : nat * nat -> nat) =
  fun (x:nat * nat) ->
    match x . 1 with
      | O _ -> x . 1
      | S _ -> add (x . 0) (f (x . 0, Un_S (x . 1)))