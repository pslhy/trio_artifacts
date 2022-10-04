fix (f : nat -> nat) = fun (x:nat) -> match x with
                                        | O _ -> x
                                        | S _ -> Un_S x