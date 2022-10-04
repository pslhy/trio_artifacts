fix (f : (nat -> nat) * list -> list) =
  fun (x:(nat -> nat) * list) ->
    match x . 1 with
      | Nil _ -> x . 1
      | Cons _ -> Cons (x . 0 (Un_Cons (x . 1) . 0),
                         f (x . 0, Un_Cons (x . 1) . 1))