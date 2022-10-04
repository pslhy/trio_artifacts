fix (f : exp -> nat) =
  fun (x:exp) ->
    match x with
      | INT _ -> Un_INT x
      | ADD _ -> add (f (Un_ADD x . 0)) Un_INT (Un_ADD x . 1)
      | MUL _ -> mul (f (Un_MUL x . 0)) Un_INT (Un_MUL x . 1)