fix (f : tree -> nat) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> 0
      | Node _ -> sum S (f (Un_Node x . 0)) (f (Un_Node x . 2))