fix (f : ) =
  fun (x0:) ->
    match x0 with
      | Node y1 -> S (max (f (y1 . 1)) (f (y1 . 2)))
      | Leaf y1 -> 0