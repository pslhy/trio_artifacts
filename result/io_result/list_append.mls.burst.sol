fix (f : list * list -> list) =
  fun (x:list * list) ->
    match x . 0 with
      | Nil _ -> x . 1
      | Cons _ -> Cons (Un_Cons (x . 0) . 0, f (Un_Cons (x . 0) . 1, x . 1))