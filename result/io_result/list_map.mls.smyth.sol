fun (x:(nat -> nat) * list) ->
  (fix (f : ) =
     fun (x1:) ->
       fun (x0:) ->
         match x0 with
           | Nil y1 -> Nil
           | Cons y1 -> (match y1 . 1 with
                           | Nil y2 -> Cons (1, Nil)
                           | Cons y2 -> Cons (x1 (y1 . 0),
                                               Cons (x1 (y1 . 0), Nil))))
    (x . 0) (x . 1)