fun (x:nat * nat) ->
  (fix (f : ) =
     fun (x1:) ->
       fun (x0:) -> match x1 with
                      | S y1 -> add (f y1 x0) x0
                      | O y1 -> 0)
    (x . 0) (x . 1)