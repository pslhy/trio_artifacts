fix (f : ) = fun (x0:) -> match x0 with
                            | S y1 -> Cons (0, f y1)
                            | O y1 -> Nil