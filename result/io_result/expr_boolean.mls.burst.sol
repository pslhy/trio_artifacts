fix (f : formula -> bool) =
  fun (x:formula) ->
    match x with
      | BOOL _ -> Un_BOOL x
      | NOT _ -> bnot Un_BOOL (Un_NOT x)
      | ANDALSO _ -> band Un_BOOL (Un_ANDALSO x . 0)
                       Un_BOOL (Un_ANDALSO x . 1)
      | ORELSE _ -> bor Un_BOOL (Un_ORELSE x . 1) Un_BOOL (Un_ORELSE x . 0)
      | IMPLY _ -> bor (bnot Un_BOOL (Un_IMPLY x . 0))
                     Un_BOOL (Un_IMPLY x . 1)