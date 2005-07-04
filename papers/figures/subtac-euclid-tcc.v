(** Hypothèses communes: *)
a : nat
mydiv : forall n : nat, n < a -> forall b : { b : nat | b <> 0 },
 { q : nat & { r : nat | div_prop n (proj1_sig b) q r } }
y : { b : nat | b <> 0 }

(** (q := 0, a ...) *)
[ H : a < proj1_sig y |- div_prop a (proj1_sig y) 0 a]

(** Argument de récursion *)
[H : a >= proj1_sig y |- a - proj1_sig y < a]

(** (q := S q', r) *)
[ H : a >= proj1_sig y
  q' : nat
  r : { r : nat | div_prop (a - proj1_sig y) (proj1_sig y) q' r }
|- div_prop a (proj1_sig y) (S q')  (proj1_sig r)]
