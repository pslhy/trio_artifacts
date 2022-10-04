fix (f : formula -> bool) =
  fun (x:formula) ->
    match x with
      | BOOL _ -> Un_BOOL x
      | NOT _ -> bnot (f Un_NOT x)
      | ANDALSO _ -> band (f (Un_ANDALSO x . 0)) (f (Un_ANDALSO x . 1))
      | ORELSE _ -> bor (f (Un_ORELSE x . 1)) (f (Un_ORELSE x . 0))
      | IMPLY _ -> bor (f (Un_IMPLY x . 1)) (bnot (f (Un_IMPLY x . 0)))