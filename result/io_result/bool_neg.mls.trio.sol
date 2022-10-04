fix (f : bool -> bool) =
  fun (x:bool) -> match x with
                    | False _ -> True
                    | True _ -> False