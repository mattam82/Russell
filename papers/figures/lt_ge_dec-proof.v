Proof (fun x y : nat =>
  sumbool_rec (fun _ : {y <= x} + {y > x} => {x < y} + {x >= y})
  (fun a : y <= x => right (x < y) a) (fun b : y > x => left (x >= y) b)
  (le_gt_dec y x)).
