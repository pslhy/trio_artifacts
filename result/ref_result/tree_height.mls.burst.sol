fix (f : tree -> nat) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> 0
      | Node _ -> S (max (f (Un_Node x . 2)) (f (Un_Node x . 1)))