fix (f : bool * bool -> bool) =
  fun (x:bool * bool) ->
    match x . 0 with
      | False _ -> x . 1
      | True _ -> (match x . 1 with
                     | False _ -> x . 0
                     | True _ -> False)