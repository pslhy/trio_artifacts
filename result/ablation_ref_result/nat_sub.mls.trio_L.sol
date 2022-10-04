fix (f : nat * nat -> nat) =
  fun (x:nat * nat) ->
    match x . 0 with
      | O _ -> x . 0
      | S _ -> (match x . 1 with
                  | O _ -> x . 0
                  | S _ -> f (Un_S (x . 0), Un_S (x . 1)))