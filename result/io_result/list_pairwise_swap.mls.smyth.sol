fix (f : ) =
  fun (x0:) ->
    match x0 with
      | Nil y1 -> Nil
      | Cons y1 -> (match y1 . 1 with
                      | Nil y2 -> Nil
                      | Cons y2 -> Cons (y2 . 0, Cons (y1 . 0, f (y2 . 1))))