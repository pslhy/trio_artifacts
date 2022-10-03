fix (f : tree -> bool) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> True
      | Node _ -> (match compare Un_S (height x)
                           (max (height (Un_Node x . 1))
                              S (height (Un_Node x . 2))) with
                     | LT _ -> f (Un_Node x . 1)
                     | EQ _ -> f (Un_Node x . 2)
                     | GT _ -> False)