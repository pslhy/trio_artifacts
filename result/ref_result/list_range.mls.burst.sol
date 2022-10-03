fix (f : nat * nat -> list) =
  fun (x:nat * nat) ->
    match compare (x . 0) (x . 1) with
      | LT _ -> (match x . 0 with
                   | O _ -> Cons (x . 0, Nil)
                   | S _ -> Nil)
      | EQ _ -> Cons (x . 0, Nil)
      | GT _ -> Cons (x . 0, f (Un_S (x . 0), x . 1))