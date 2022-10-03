fix (f : bool * bool -> bool) =
  fun (x:bool * bool) -> match x . 0 with
                           | False _ -> True
                           | True _ -> x . 1