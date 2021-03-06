Require Export Coq.Arith.Max.
Require Import Omega.

Set Implicit Arguments.

Definition max3 n m p := max n (max m p).
Definition max4 n m p q := max n (max3 m p q).
Definition max5 n m p q r := max n (max4 m p q r).

Lemma max_lt_l : forall m n, m < S (max m n).
Proof.
  intros.
  rewrite max_SS.
  pose (le_max_l (S m) (S n)).
  omega.
Qed.

Lemma max_lt_r : forall m n, n < S (max m n).
Proof.
  intros.
  rewrite max_SS.
  pose (le_max_r (S m) (S n)).
  omega.
Qed.

Hint Resolve max_lt_l max_lt_r : arith.

Lemma max3_lt_1 : forall m n p, m < S (max3 m n p).
Proof.
  unfold max3 ; auto with arith.
Qed.

Lemma max_n_0_n : forall m, max m 0 = m.
Proof.
  induction m ; simpl ; auto with arith.
Qed.

Lemma max3_commut_1 : forall n m p, max3 n m p = max3 m p n.
Proof.
  induction n ; unfold max3 ; auto with arith.
  simpl.
  intros.
  rewrite max_n_0_n.
  reflexivity.
  intros.
  destruct m ; destruct p ; simpl ; auto with arith.
  rewrite max_comm ; auto.
  rewrite max_comm ; auto.
  unfold max3 in IHn ; rewrite IHn.
  reflexivity.
Qed.

Lemma max3_commut_2 : forall n m p, max3 n m p = max3 p m n.
Proof.
  induction n ; unfold max3 ; auto with arith.
  simpl.
  intros.
  rewrite max_n_0_n.
  rewrite max_comm ; reflexivity.
  intros.
  destruct m ; destruct p ; simpl ; auto with arith.
  rewrite max_comm ; auto.
  rewrite max_comm ; auto.
  unfold max3 in IHn ; rewrite IHn.
  reflexivity.
Qed.

Lemma max3_lt_2 : forall m n p, n < S (max3 m n p).
Proof.
  intros.
  rewrite max3_commut_1.
  unfold max3 ; auto with arith.
Qed.

Lemma max3_lt_3 : forall m n p, p < S (max3 m n p).
Proof.
  intros.
  rewrite max3_commut_2.
  unfold max3 ; auto with arith.
Qed.

Lemma max4_commut_1 : forall n m p q, max4 n m p q = max4 m p q n.
Proof.
  induction n ; unfold max4 ; auto with arith.
  simpl.
  intros.
  unfold max3 ; rewrite max_n_0_n.
  reflexivity.
  intros.
  destruct m ; destruct p ; destruct q ; simpl ; auto with arith.
  unfold max3 ; rewrite max_comm ; auto.
  unfold max3 ; rewrite max_comm ; auto.
  rewrite max3_commut_2.
  unfold max3 ; simpl ; auto with arith.
  pattern (max q p) ; rewrite max_comm ; auto with arith.
  rewrite max_comm ; auto.
  pose (max3_commut_1).
  unfold max3 in e.
  rewrite e ; auto.

  pose (max3_commut_1).
  unfold max3 in e.
  rewrite e ; auto.
  unfold max4, max3 in IHn ; rewrite IHn.
  reflexivity.
Qed.

Lemma max4_commut_2 : forall n m p q, max4 n m p q = max4 p q n m.
Proof.
  induction n ; unfold max4 ; auto with arith.
  simpl.
  intros.
  unfold max3 ; simpl.
  pose (max3_commut_1).
  unfold max3 in e.
  rewrite e ; auto.
  intros.
  destruct m ; destruct p ; destruct q ; simpl ; auto with arith.
  unfold max3 ; rewrite max_comm ; auto.
  unfold max3 ; rewrite max_comm ; auto.
  pose max3_commut_1.
  unfold max3 in e.
  rewrite e ; auto.
  unfold max3 ; simpl ; auto with arith.
  pose max3_commut_2.
  unfold max3 in e.
  rewrite e.
  pattern (max n m) ; rewrite max_comm ; auto with arith.
  pose max3_commut_2.
  unfold max3 in e.
  rewrite e.
  pattern (max n m) ; rewrite max_comm ; auto with arith.
  unfold max4, max3 in IHn ; rewrite IHn.
  reflexivity.
Qed.

Lemma max4_commut_3 : forall n m p q, max4 n m p q = max4 q n m p.
Proof.
  induction n ; unfold max4 ; auto with arith.
  simpl.
  intros.
  unfold max3 ; simpl.
  pose (max3_commut_1).
  unfold max3 in e.
  rewrite e ; auto.
  intros.
  destruct m ; destruct p ; destruct q ; simpl ; auto with arith.
  unfold max3 ; rewrite max_comm ; auto.
  pose (max3_commut_1) ; unfold max3 in e ; rewrite e ; auto.
  pose (max3_commut_1) ; unfold max3 in e ; rewrite e ; auto.
  unfold max4, max3 in IHn ; rewrite IHn.
  reflexivity.
Qed.

Lemma max4_lt_1 : forall m n p q, m < S (max4 m n p q).
Proof.
  intros.
  unfold max4 ; auto with arith.
Qed.

Lemma max4_lt_2 : forall m n p q, n < S (max4 m n p q).
Proof.
  intros.
  rewrite max4_commut_1.
  unfold max4 ; auto with arith.
Qed.

Lemma max4_lt_3 : forall m n p q, p < S (max4 m n p q).
Proof.
  intros.
  rewrite max4_commut_2.
  unfold max4 ; auto with arith.
Qed.

Lemma max4_lt_4 : forall m n p q, q < S (max4 m n p q).
Proof.
  intros.
  rewrite max4_commut_3.
  unfold max4 ; auto with arith.
Qed.

Lemma max_commut_2 : forall m n p, max m (max n p) = max n (max m p).
Proof.
  intros.
  pose max3_commut_1.
  unfold max3 in e.
  rewrite (e m n p).
  pattern (max m p) ; rewrite max_comm.
  reflexivity.
Qed.

Lemma max5_commut : forall n m p q r, max5 n m p q r = max5 m p q r n.
Proof.
  intros.
  unfold max5.
  unfold max4.
  rewrite max_commut_2.
  pose (max4_commut_1).
  unfold max4 in e.
  unfold max3 in e.
  unfold max3.
  pattern (max p (max q (max r n))).
  rewrite <- e.
  reflexivity.
Qed.

Lemma max5_commut_2 : forall n m p q r, max5 n m p q r = max5 p q r n m.
Proof.
  intros.
  rewrite max5_commut.
  rewrite max5_commut.
  auto.
Qed.

Lemma max5_commut_3 : forall n m p q r, max5 n m p q r = max5 q r n m p.
Proof.
  intros.
  rewrite max5_commut.
  rewrite max5_commut.
  rewrite max5_commut.
  reflexivity.
Qed.

Lemma max5_commut_4 : forall n m p q r, max5 n m p q r = max5 r n m p q.
Proof.
  intros.
  rewrite max5_commut.
  rewrite max5_commut.
  rewrite max5_commut.
  rewrite max5_commut.
  reflexivity.
Qed.

Lemma max5_lt_1 : forall m n p q r, m < S (max5 m n p q r).
Proof.
  intros.
  unfold max5 ; auto with arith.
Qed.

Lemma max5_lt_2 : forall m n p q r, n < S (max5 m n p q r).
Proof.
  intros.
  rewrite max5_commut.
  unfold max5 ; auto with arith.
Qed.

Lemma max5_lt_3 : forall m n p q r, p < S (max5 m n p q r).
Proof.
  intros.
  rewrite max5_commut_2.
  unfold max5 ; auto with arith.
Qed.

Lemma max5_lt_4 : forall m n p q r, q < S (max5 m n p q r).
Proof.
  intros.
  rewrite max5_commut_3.
  unfold max5 ; auto with arith.
Qed.

Lemma max5_lt_5 : forall m n p q r, r < S (max5 m n p q r).
Proof.
  intros.
  rewrite max5_commut_4.
  unfold max5 ; auto with arith.
Qed.

Hint Resolve max3_lt_1 max3_lt_2 max3_lt_3 : arith.
Hint Resolve max4_lt_1 max4_lt_2 max4_lt_3 max4_lt_4 : arith.
Hint Resolve max5_lt_1 max5_lt_2 max5_lt_3 max5_lt_4 max5_lt_5 : arith.
