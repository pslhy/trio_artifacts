fix (f : tree -> nat) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> 1
      | Node _ -> sum (f (Un_Node x . 0)) (f (Un_Node x . 2))