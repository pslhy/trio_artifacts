fix (f : tree -> bool) =
  fun (x:tree) ->
    match x with
      | Leaf _ -> True
      | Node _ -> (match Un_Node x . 1 with
                     | Leaf _ -> True
                     | Node _ -> (match compare
                                          (height
                                             (Un_Node (Un_Node x . 1) . 2))
                                          1 with
                                    | EQ _ -> True
                                    | GT _ -> False
                                    | LT _ -> (match Un_Node (Un_Node x . 1)
                                                       . 1 with
                                                 | Leaf _ -> True
                                                 | Node _ -> False)))