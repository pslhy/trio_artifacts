fun (x:tree * nat) ->
  (fix (f : ) =
     fun (x1:) ->
       fun (x0:) ->
         match x1 with
           | Node y1 -> (match x0 with
                           | S y2 -> sum (f (y1 . 0) y2) (f (y1 . 2) y2)
                           | O y2 -> S x0)
           | Leaf y1 -> 0)
    (x . 0) (x . 1)