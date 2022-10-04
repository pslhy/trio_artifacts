fix (f : ) =
  fun (x0:) ->
    match x0 with
      | Node y1 -> add (add (f (y1 . 1)) (f (y1 . 2))) (y1 . 0)
      | Leaf y1 -> 0