fix (f : tree -> nat) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> 0
      | Node _ -> sum (f (Un_Node x . 0)) S (f (Un_Node x . 2))