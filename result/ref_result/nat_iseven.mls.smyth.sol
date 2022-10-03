fix (f : ) =
  fun (x0:) ->
    match x0 with
      | S y1 -> (match y1 with
                   | S y2 -> f y2
                   | O y2 -> False)
      | O y1 -> True