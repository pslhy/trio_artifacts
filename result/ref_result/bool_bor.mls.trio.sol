fix (f : bool * bool -> bool) =
  fun (x:bool * bool) -> match x . 0 with
                           | False _ -> x . 1
                           | True _ -> x . 0