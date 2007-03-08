Require Import Coq.subtac.Utils.
Require Import Wf_nat.
Require Import Arith.
Require Import Omega.
Set Implicit Arguments.
Set Strict Implicit.

Print right.

Program Definition less_than (x y : nat) : 
  { x < y } + { x >= y} :=
  if le_lt_dec y x then right _ _ else left _ _.

Notation "{ ( x , y )  :  A  |  P }" := 
  (sig (fun t:A => let (x,y) := t in P))
  (x ident, y ident) : type_scope.

Program Fixpoint div (a : nat) (b : nat | b <> 0)
  { wf lt } :
  { (q, r) : nat * nat | a = b * q + r /\ r < b } :=
  if less_than a b then
    (O, a)
  else
    dest div (a - b) b as (q', r) in (S q', r).

Solve Obligations using subtac_simpl ; auto with *.

Next Obligation.
Proof.
  intros.
  destruct_call div ; subtac_simpl.
  assert(x * S q' = (x * q') + x) by
    auto with arith.
  omega.
Qed.

Print div.

Extraction Inline less_than.
Recursive Extraction div.

Program Definition divides
  (x : nat) (y : nat | y <> 0) := 
  dest div x y as (q, r) in r = 0.

Lemma mult_n_m_0 : forall n m, mult n m = 0 ->  n = 0 \/ m = 0.
Proof.
  destruct n ; destruct m ; simpl in * ; intuition.
  discriminate.
Qed.

Program Definition divides_mult_stmt :=
  forall (r : nat) (p : nat | p <> 0) (q : nat | q <> 0),
  divides r (p * q) -> divides r p.

Next Obligation.
Proof.
  intros.
  red ; intros.
  pose (mult_n_m_0 _ _ H) ; intuition.
Qed.

Axiom euclidian_decomp_unicity : 
  forall c p c' r q, c > 0 -> c' > 0 ->
  c * p + r = c * c' * q -> r < c -> 
  r = 0.

Lemma divides_mult : divides_mult_stmt.
Proof.
  red ; intros.
  unfold divides in * ; subtac_simpl ;
    repeat destruct_call div ; simpl in *.
  destruct x1 ; destruct x2.
  subst.
  intuition.
  subst r.
  replace (x0 * x * n1 + 0) with (x0 * x * n1) in H1 ; try omega.
  apply (@euclidian_decomp_unicity x0 n3 x n4 n1) ; try omega.
Qed.

