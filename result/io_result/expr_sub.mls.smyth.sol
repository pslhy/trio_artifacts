fix (f : ) =
  fun (x0:) ->
    match x0 with
      | SUB y1 -> S (sub 4 (f (y1 . 1)))
      | MUL y1 -> S (S (S (S (S (S (sub (f (y1 . 0)) 4))))))
      | INT y1 -> S (sub (mul y1 y1) y1)
      | ADD y1 -> 7