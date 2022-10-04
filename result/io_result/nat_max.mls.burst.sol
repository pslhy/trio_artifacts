fix (f : nat * nat -> nat) =
  fun (x:nat * nat) ->
    match compare (x . 1) (x . 0) with
      | LT _ -> x . 0
      | EQ _ -> x . 0
      | GT _ -> x . 1