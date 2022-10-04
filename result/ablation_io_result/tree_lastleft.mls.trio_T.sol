fix (f : tree -> nat) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> 0
      | Node _ -> (match Un_Node x . 1 with
                     | Leaf _ -> Un_Node x . 0
                     | Node _ -> f (Un_Node x . 1))