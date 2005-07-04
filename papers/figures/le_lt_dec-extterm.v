let rec le_lt_dec n y =
  match n with
    | O -> Left
    | S n0 -> (match y with
                 | O -> Right
                 | S y0 -> le_lt_dec n0 y0)
