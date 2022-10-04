fix (f : list -> list) =
  fun (x:list) ->
    match x with
      | Nil _ -> x
      | Cons _ -> append (f (Un_Cons x . 1)) Cons (Un_Cons x . 0, Nil)