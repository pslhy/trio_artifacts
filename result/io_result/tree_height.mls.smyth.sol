fix (f : ) =
  fun (x0:) ->
    match x0 with
      | Node y1 -> S (match y1 . 2 with
                        | Node y2 -> S (max (f (y2 . 2)) S (y1 . 0))
                        | Leaf y2 -> f (y1 . 1))
      | Leaf y1 -> 0