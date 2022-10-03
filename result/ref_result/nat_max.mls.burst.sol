fix (f : nat * nat -> nat) =
  fun (x:nat * nat) ->
    match compare (x . 0) (x . 1) with
      | LT _ -> x . 1
      | EQ _ -> x . 0
      | GT _ -> x . 0