fix (f : tree -> list) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> Nil
      | Node _ -> append (append (f (Un_Node x . 0)) (f (Un_Node x . 2)))
                    Cons (Un_Node x . 1, Nil)