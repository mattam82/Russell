(** Hypothèses communes: *)
a : nat
mydiv : forall n : nat, n < a -> forall b : { b : nat | b <> 0 },
 { q : nat & { r : nat | div_prop n (proj1_sig b) q r } }
b : { b : nat | b <> 0 }

(**1 (q := 0, a ...) *)
[ H : a < proj1_sig b |- div_prop a (proj1_sig b) 0 a]

(**2 Argument de récursion *)
[H : a >= proj1_sig b |- a - proj1_sig b < a]

(**3 (q := S q', r) *)
[ H : a >= proj1_sig b
  q' : nat
  r : { r : nat | div_prop (a - proj1_sig b) (proj1_sig b) q' r }
|- div_prop a (proj1_sig b) (S q')  (proj1_sig r)]
