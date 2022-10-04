fun (x:(nat -> nat -> nat) * nat * list) ->
  (fix (f : ) =
     fun (x2:) ->
       fun (x1:) ->
         fun (x0:) ->
           match x0 with
             | Nil y1 -> 0
             | Cons y1 -> S (count_odd (count_odd (y1 . 0) (y1 . 0)) (y1 . 0)))
    (x . 0) (x . 1) (x . 2)