fix (f : list * nat -> list) =
  fun (x:list * nat) ->
    match x . 0 with
      | Nil _ -> Cons (x . 1, x . 0)
      | Cons _ -> Cons (Un_Cons (x . 0) . 0, f (Un_Cons (x . 0) . 1, x . 1))