fix (f : nat * tree -> bool) =
  fun (x:nat * tree) ->
    match x . 1 with
      | Leaf _ -> True
      | Node _ -> (match compare (x . 0) (Un_Node (x . 1) . 0) with
                     | LT _ -> band (f (x . 0, Un_Node (x . 1) . 1))
                                 (f (x . 0, Un_Node (x . 1) . 2))
                     | EQ _ -> False
                     | GT _ -> band (f (x . 0, Un_Node (x . 1) . 1))
                                 (f (x . 0, Un_Node (x . 1) . 2)))