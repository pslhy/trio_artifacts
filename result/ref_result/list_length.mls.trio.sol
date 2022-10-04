fix (f : list -> nat) =
  fun (x:list) -> match x with
                    | Nil _ -> 0
                    | Cons _ -> S (f (Un_Cons x . 1))