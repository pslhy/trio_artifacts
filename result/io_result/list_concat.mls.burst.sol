fix (f : llist -> list) =
  fun (x:llist) ->
    match x with
      | LNil _ -> Nil
      | LCons _ -> append (Un_LCons x . 0) (f (Un_LCons x . 1))