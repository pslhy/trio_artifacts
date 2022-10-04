fix (f : ) =
  fun (x0:) ->
    match x0 with
      | Node y1 -> (match y1 . 1 with
                      | Node y2 -> f (y1 . 1)
                      | Leaf y2 -> y1 . 0)
      | Leaf y1 -> 0