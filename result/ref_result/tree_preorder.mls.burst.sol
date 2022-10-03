fix (f : tree -> list) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> Nil
      | Node _ -> Cons (Un_Node x . 1,
                         append (f (Un_Node x . 0)) (f (Un_Node x . 2)))