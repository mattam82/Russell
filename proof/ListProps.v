Require Import Coq.Lists.List.
Require Import CCP.Axioms.
Lemma nth_cons : forall A : Set, forall i l d, forall x : A,
 nth i l d = nth (S i) (x :: l) d.
Proof.
  intros ; induction l ; induction i ; simpl ; auto.
Qed.

Lemma length_0_nil : forall A : Set, forall l : list A, length l = 0 -> l = nil.
Proof.
  induction l ; intros ; simpl ; auto.
  simpl in H.
  discriminate.
Qed.

Require Import Coq.Arith.Arith.

Lemma leq_0_S : forall i, ~ (0 >= S i).
Proof.
  intros.
  unfold ge.
  auto with arith.
Qed.

Lemma nth_app_middle : forall A : Set, forall x d : A, forall l l' i,  i >= length l -> 
  nth (S i) (l ++ x :: l') d = nth i (l ++ l') d.
Proof.
  induction l ; simpl ; intros ; auto.
  induction i.
  elim (leq_0_S _ H).
  rewrite (IHl l' i) ; auto with arith.
Qed.

Lemma length_app : forall A : Set, forall l l' : list A, length (l ++ l') = length l + length l'.
Proof.
  intros.
  induction l.
  simpl ; auto.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Require Import Omega.

Lemma nth_i_app : forall A : Set, forall d : A, forall l' l i, 
  nth i l d = nth (length l' + i) (l' ++ l) d.
Proof.
  induction l' using rev_ind.
  intros.
  simpl.
  reflexivity.
  intros.
  rewrite app_ass ;  simpl.
  rewrite (length_app A l' (x :: nil)).
  simpl.
  rewrite IHl'.
  assert(length l' + 1 + i = S (length l' + i)) ; try omega.
  rewrite H.
  rewrite (nth_app_middle A x d).
  reflexivity.
  auto with arith.
Qed.









  