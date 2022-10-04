fix (f : tree -> nat) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> 0
      | Node _ -> max S (f (Un_Node x . 1)) S (f (Un_Node x . 2))