fix (f : tree -> list) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> Nil
      | Node _ -> append Cons (Un_Node x . 1, f (Un_Node x . 0))
                    (f (Un_Node x . 2))