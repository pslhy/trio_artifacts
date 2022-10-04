fun (x:(nat -> nat) * tree) ->
  (fix (f : ) =
     fun (x1:) ->
       fun (x0:) ->
         match x0 with
           | Node y1 -> Node (match y1 . 0 with
                                | Node y2 -> Node (Leaf, 1, Leaf)
                                | Leaf y2 -> Leaf,
                               x1 (y1 . 1),
                               match y1 . 2 with
                                 | Node y2 -> Node (Leaf, 1, Leaf)
                                 | Leaf y2 -> Leaf)
           | Leaf y1 -> Leaf)
    (x . 0) (x . 1)