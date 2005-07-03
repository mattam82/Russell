Require Import Coq.Arith.Arith.
Definition neq (A : Set) (x y : A) := x <> y.
Definition div_prop (a b q r : nat) := r < b /\ a = b * q + r.
Definition lt_ge_dec (x y : nat) : { x < y } + { x >= y }.
intros ; elim (le_gt_dec y x) ; auto with arith.
Save.

Recursive program mydiv (a : nat) using lt proof lt_wf : { b : nat | neq nat b O } ->
  [ q : nat ] { r : nat | div_prop a b q r } :=
  fun { b : nat | neq nat b O } =>
    if lt_ge_dec a b
      then (q := O, a : { r : nat | div_prop a b q r })
      else let (q', r) = mydiv (minus a b) b in
        (q := S q', r : { r : nat | div_prop a b q r }).
  
(* Dans Coq, mydiv aura le type:
forall a : nat, forall b : { b : nat | b <> 0 },
 { q : nat & { r : nat | div_prop a (proj1_sig b) q r } } *)

(* Obligations de preuves engendrées *)
(* Hypothèses communes: *)
a : nat
mydiv : (n : nat) n < a -> forall b : { b : nat | b <> 0 },
 { q : nat & { r : nat | div_prop n (proj1_sig b) q r } }
y : { b : nat | b <> 0 }

(* (q := 0, a ...) *)
[ H : a < proj1_sig y,
|- div_prop a (proj1_sig y) 0 a]

(* Argument de récursion *)
[H : a >= proj1_sig y |- a - proj1_sig y < a]

(* (q := S q', r) *)
[ H : a >= proj1_sig y
  q' : nat
  r : { r : nat | div_prop (a - proj1_sig y) (proj1_sig y) q' r }
|- div_prop a (proj1_sig y) (S q')  (proj1_sig r)]
