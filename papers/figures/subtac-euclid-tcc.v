(** Hypothèses communes: *)
a : nat
mydiv : forall n : nat, n < a -> forall b : { b : nat | b <> 0 },
 { q : nat & { r : nat | div_prop n (pi_1 b) q r } }
b : { b : nat | b <> 0 }

(**1 (q := 0, a ...) *)
[ H : a < pi_1 b |- div_prop a (pi_1 b) 0 a]

(**2 Argument de récursion *)
[H : a >= pi_1 b |- a - pi_1 b < a]

(**3 (q := S q', r) *)
[ H : a >= pi_1 b
  q' : nat
  r : { r : nat | div_prop (a - pi_1 b) (pi_1 b) q' r }
|- div_prop a (pi_1 b) (S q')  (pi_1 r)]
