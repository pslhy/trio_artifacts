fix (f : llist -> list) =
  fun (x:llist) ->
    match x with
      | LNil _ -> Nil
      | LCons _ -> append (f (Un_LCons x . 1)) (Un_LCons x . 0)