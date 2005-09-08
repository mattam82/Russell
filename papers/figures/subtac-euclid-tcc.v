(** Hypothèses communes: *)
a : nat
mydiv : forall n : nat, n < a -> forall b : { b : nat | b <> 0 },
 { (q, r) : nat * nat | div_prop n (pi_1 b) q r }
b : { b : nat | b <> 0 }

(** (q := 0, a ...) *)
[ H : a < pi_1 b |- div_prop a (pi_1 b) 0 a ]

(** Argument de récursion *)
[ H : a >= pi_1 b |- a - pi_1 b < a ]

(** (q := S q', r) *)
[ H : a >= pi_1 b, q' : nat
  r : { r : nat | div_prop (a - pi_1 b) (pi_1 b) q' r }
|- div_prop a (pi_1 b) (S q')  (pi_1 r)]
