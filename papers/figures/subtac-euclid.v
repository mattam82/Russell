Definition div_prop (a b q r : nat) := r < b /\ a = b * q + r.

Recursive program mydiv (a : nat) { wf lt proof lt_wf } :
  { b : nat | b <> O } -> { (q, r) : nat * nat | div_prop a b q r } :=
  fun { b : nat | b <> O } =>
    if lt_ge_dec a b
      then (q := O, a : { r : nat | div_prop a b q r })
      else let (q', r) = mydiv (minus a b) b in
        (q := S q', r : { r : nat | div_prop a b q r }).
  
(** Dans Coq, mydiv aura le type: *)
forall a : nat, forall b : { b : nat | b <> 0 },
  { (q, r) : nat * nat | div_prop a (pi_1 b) q r } 
