fix (f : list -> nat) =
  fun (x:list) -> match x with
                    | Nil _ -> 0
                    | Cons _ -> Un_Cons x . 0