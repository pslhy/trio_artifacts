fix (f : list -> list) =
  fun (x:list) -> match x with
                    | Nil _ -> x
                    | Cons _ -> Un_Cons x . 1