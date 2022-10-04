fix (f : tree -> nat) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> 0
      | Node _ -> add (f (Un_Node x . 1))
                    (add (f (Un_Node x . 2)) (Un_Node x . 0))