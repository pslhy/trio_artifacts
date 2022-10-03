fix (f : nat * nat -> nat) =
  fun (x:nat * nat) ->
    match compare (x . 0) (x . 1) with
      | EQ _ -> x . 0
      | GT _ -> x . 0
      | LT _ -> x . 1