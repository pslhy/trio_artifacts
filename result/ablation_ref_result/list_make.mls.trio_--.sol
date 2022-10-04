fix (f : nat -> list) =
  fun (x:nat) -> match x with
                   | O _ -> Nil
                   | S _ -> Cons (0, f Un_S x)