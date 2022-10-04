fix (f : tree -> nat) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> 0
      | Node _ -> (match Un_Node x . 2 with
                     | Leaf _ -> S (f (Un_Node x . 1))
                     | Node _ -> max S (f (Un_Node x . 2))
                                   S (S (f (Un_Node x . 1))))