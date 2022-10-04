fun (x:(nat -> bool) * list) ->
  (fix (f : ) =
     fun (x1:) ->
       fun (x0:) ->
         match x1 0 with
           | True y1 -> (match x0 with
                           | Nil y2 -> Nil
                           | Cons y2 -> (match is_even (y2 . 0) with
                                           | True y3 -> x0
                                           | False y3 -> Cons (0, Nil)))
           | False y1 -> Nil)
    (x . 0) (x . 1)