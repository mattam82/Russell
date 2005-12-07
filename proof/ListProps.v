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