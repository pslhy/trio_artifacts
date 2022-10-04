fix (f : tree * nat -> nat) =
  fun (x:tree * nat) ->
    match x . 0 with
      | Leaf _ -> 0
      | Node _ -> (match x . 1 with
                     | O _ -> S (x . 1)
                     | S _ -> sum (f (Un_Node (x . 0) . 0, Un_S (x . 1)))
                                (f (Un_Node (x . 0) . 2, Un_S (x . 1))))