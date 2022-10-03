fix (f : ) =
  fun (x0:) ->
    match x0 with
      | Nil y1 -> True
      | Cons y1 -> (match y1 . 0 with
                      | True y2 -> bnot (f (y1 . 1))
                      | False y2 -> f (y1 . 1))