fix (f : (nat -> nat) * tree -> tree) =
  fun (x:(nat -> nat) * tree) ->
    match x . 1 with
      | Leaf _ -> x . 1
      | Node _ -> Node (f (x . 0, Un_Node (x . 1) . 0),
                         x . 0 (Un_Node (x . 1) . 1),
                         f (x . 0, Un_Node (x . 1) . 2))