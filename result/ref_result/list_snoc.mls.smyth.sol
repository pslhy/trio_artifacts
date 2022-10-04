fun (x:list * nat) ->
  (fix (f : ) =
     fun (x1:) ->
       fun (x0:) ->
         Cons (match x1 with
                 | Nil y1 -> (x0, Nil)
                 | Cons y1 -> (y1 . 0, f (y1 . 1) x0)))
    (x . 0) (x . 1)