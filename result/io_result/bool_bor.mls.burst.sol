fix (f : bool * bool -> bool) =
  fun (x:bool * bool) -> match x . 1 with
                           | False _ -> x . 0
                           | True _ -> x . 1