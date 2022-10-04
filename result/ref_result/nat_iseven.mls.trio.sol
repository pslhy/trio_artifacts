fix (f : nat -> bool) =
  fun (x:nat) ->
    match x with
      | O _ -> True
      | S _ -> (match Un_S x with
                  | O _ -> False
                  | S _ -> f Un_S (Un_S x))