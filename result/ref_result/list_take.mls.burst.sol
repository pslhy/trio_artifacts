fix (f : nat * list -> list) =
  fun (x:nat * list) ->
    match x . 0 with
      | O _ -> Nil
      | S _ -> (match x . 1 with
                  | Nil _ -> x . 1
                  | Cons _ -> Cons (Un_Cons (x . 1) . 0,
                                     f (Un_S (x . 0), Un_Cons (x . 1) . 1)))