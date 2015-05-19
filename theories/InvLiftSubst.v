Require Import Lambda.Utils.
Require Import Lambda.Tactics.

Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Conv_Dec.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.

Set Implicit Arguments.

Lemma inv_lift_prod : forall t U V n, lift n t = Prod U V ->
 exists U', exists V', t = Prod U' V' /\ U = (lift_rec n U' 0) /\ V = (lift_rec n V' 1).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t1 ; exists t2 ; split ; [auto | split ; auto].
Qed.

Lemma inv_lift_sum : forall t U V n, lift n t = Sum U V ->
 exists U', exists V', t = Sum U' V' /\ U = (lift_rec n U' 0) /\ V = (lift_rec n V' 1).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t1 ; exists t2 ; split ; [auto | split ; auto].
Qed.

Lemma inv_lift_subset : forall t U V n, lift n t = Subset U V ->
 exists U', exists V', t = Subset U' V' /\ U = (lift_rec n U' 0) /\ V = (lift_rec n V' 1).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t1 ; exists t2 ; split ; [auto | split ; auto].
Qed.

Lemma inv_lift_abs : forall t U V n, lift n t = Abs U V ->
 exists U', exists V', t = Abs U' V' /\ U = (lift_rec n U' 0) /\ V = (lift_rec n V' 1).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t1 ; exists t2 ; split ; [auto | split ; auto].
Qed.

Lemma inv_lift_app : forall t U V n, lift n t = App U V ->
 exists U', exists V', t = App U' V' /\ U = (lift_rec n U' 0) /\ V = (lift_rec n V' 0).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t1 ; exists t2 ; split ; [auto | split ; auto].
Qed.

Lemma inv_lift_pair : forall t U V W n, lift n t = Pair U V W ->
 exists3 U' V' W', t = Pair U' V' W' /\ U = (lift_rec n U' 0) /\ V = (lift_rec n V' 0) /\ W = (lift_rec n W' 0).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t1 t2 t3 ; split ; [auto | split ; auto].
Qed.

Lemma inv_lift_pi1 : forall t U n, lift n t = Pi1 U ->
 exists U', t = Pi1 U' /\ U = (lift_rec n U' 0).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t ; split ; [auto | auto].
Qed.

Lemma inv_lift_pi2 : forall t U n, lift n t = Pi2 U ->
 exists U', t = Pi2 U' /\ U = (lift_rec n U' 0).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t ; split ; [auto | auto].
Qed.

Lemma inv_lift_sort : forall t s n, lift n t = Srt s -> t = Srt s.
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
auto.
Qed.

Lemma inv_subst_sort : forall t t' n s, subst_rec t t' n = Srt s -> 
  t = Srt s \/ t' = Srt s.
Proof.
  induction t' ;  simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  generalize H.
  elim (lt_eq_lt_dec n0 n).
  intros a ; case a ; clear a ; intros ; try discriminate ; auto.
  left.
  exact (inv_lift_sort _ _ H0).
  intros.
  discriminate.
Qed.
