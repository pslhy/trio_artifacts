fix (f : tree * nat -> tree) =
  fun (x:tree * nat) ->
    match x . 0 with
      | Leaf _ -> Node (x . 0, x . 1, x . 0)
      | Node _ -> (match comp_nat (x . 1) (Un_Node (x . 0) . 1) with
                     | CEq _ -> x . 0
                     | CGt _ -> Node (f (Un_Node (x . 0) . 0, x . 1),
                                       Un_Node (x . 0) . 1,
                                       Un_Node (x . 0) . 2)
                     | CLt _ -> Node (Un_Node (x . 0) . 0,
                                       Un_Node (x . 0) . 1,
                                       f (Un_Node (x . 0) . 2, x . 1)))