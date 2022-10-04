fix (f : ) =
  fun (x0:) ->
    match x0 with
      | Nil y1 -> Nil
      | Cons y1 -> (match is_even (y1 . 0) with
                      | True y2 -> y1 . 1
                      | False y2 -> Cons (y1 . 0, f (y1 . 1)))