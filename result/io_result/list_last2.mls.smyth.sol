fix (f : ) =
  fun (x0:) ->
    match x0 with
      | Nil y1 -> None
      | Cons y1 -> (match y1 . 1 with
                      | Nil y2 -> None
                      | Cons y2 -> (match y2 . 1 with
                                      | Nil y3 -> Some (y1 . 0, y2 . 0)
                                      | Cons y3 -> f (y1 . 1)))