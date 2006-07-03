Require Import Lambda.Utils.
Require Import Lambda.Tactics.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Basic.
Require Import Lambda.TPOSR.Thinning.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.Coercion.
Require Import Lambda.TPOSR.Equiv.
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.CtxConversion.
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.ChurchRosser.
Require Import Lambda.TPOSR.CoerceDepth.
Require Import Lambda.TPOSR.Transitivity.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.

Corollary injectivity_of_pi_coerce_rc_depth_aux : forall e T U s n,
  e |-- T >-> U : s [n] ->
  forall A A' B B', e |-- T ~= Prod_l A B : s -> e |-- U ~= Prod_l A' B' : s ->
  exists s1, e |-- A' >-> A : s1 /\ A' :: e |-- B >-> B' : s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc ; try discriminate.
  subst.

  pose (tposr_eq_trans (tposr_eq_sym H0) H1).
  pose (injectivity_of_pi t) ; destruct_exists.
  exists x.
  split ; auto with coc.
  apply coerce_conv_env with (A0 :: e) ; auto with coc.
  apply conv_env_hd with x ; auto with coc.

  pose (injectivity_of_pi H5).
  pose (injectivity_of_pi H6).
  destruct_exists.
  pose (coerce_rc_depth_coerce H).
  pose (coerce_rc_depth_coerce H2).
  rewrite <- (unique_sort (coerce_refl_r t) (conv_refl_l H8)) in H8.
  rewrite <- (unique_sort (coerce_refl_l t) (conv_refl_l H7)) in H7.
  exists s ; split.
  apply tposr_coerce_trans with A' ; auto with coc.
  apply tposr_coerce_trans with A ; auto with coc.
  assert(A' :: e |-- B ~= B0 : s').
  apply eq_coerce_env with (A :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  apply coerce_coerce_env with (A' :: e) ; auto with coc.
  apply tposr_coerce_trans with B ; auto with coc.
  apply tposr_coerce_trans with B' ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.

  elim conv_prod_sum with A0 B0 A B.
  pose (tposr_eq_conv H7) ; auto with coc.

  elim conv_prod_subset with A B U P.
  pose (tposr_eq_conv H1) ; auto with coc.

  elim conv_prod_subset with A' B' U' P.
  pose (tposr_eq_conv H2) ; auto with coc.

  apply IHcoerce_rc_depth ; auto.
  apply tposr_eq_trans with A ; auto with coc.

  apply IHcoerce_rc_depth ; auto.
  apply tposr_eq_trans with C ; auto with coc.
Qed.

Corollary injectivity_of_pi_coerce : forall e A A' B B' s, 
  e |-- Prod_l A B >-> Prod_l A' B' : s ->
  exists s1, e |-- A' >-> A : s1 /\ A' :: e |-- B >-> B' : s.
Proof.
  intros.
  destruct (coerce_coerce_rc_depth H).
  eapply injectivity_of_pi_coerce_rc_depth_aux with (Prod_l A B) (Prod_l A' B') x ; auto.
  apply tposr_eq_tposr ; apply (coerce_refl_l H).
  apply tposr_eq_tposr ; apply (coerce_refl_r H).
Qed.

Corollary injectivity_of_sum_coerce_rc_depth_aux : forall e T U s n,
  e |-- T >-> U : s [n] ->
  forall A A' B B', e |-- T ~= Sum_l A B : s -> e |-- U ~= Sum_l A' B' : s ->
  exists2 s1 s2, e |-- A >-> A' : s1 /\ A :: e |-- B >-> B' : s2 /\
  sum_sort s1 s2 s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc ; try discriminate.
  subst.

  pose (tposr_eq_trans (tposr_eq_sym H0) H1).
  pose (injectivity_of_sum t) ; destruct_exists.
  exists a b.
  intuition ; auto with coc.

  elim conv_prod_sum with A B A0 B0.
  pose (tposr_eq_conv H5) ; auto with coc.

  pose (injectivity_of_sum H7).
  pose (injectivity_of_sum H8).
  destruct_exists.
  pose (coerce_rc_depth_coerce H).
  pose (coerce_rc_depth_coerce H2).
  rewrite <- (unique_sort (coerce_refl_l t) (conv_refl_l H10)) in H10.
  rewrite <- (unique_sort (coerce_refl_r t) (conv_refl_l H9)) in H9.
  rewrite <- (unique_sort (coerce_refl_l t0) (conv_refl_l H13)) in H13.
  assert(A :: e |-- B' ~= B'0 : b).
  apply eq_coerce_env with (A' :: e) ; auto with coc.
  eauto with coc.
  rewrite <- (unique_sort (coerce_refl_r t0) (conv_refl_l H15)) in H11.
  rewrite <- (unique_sort (coerce_refl_r t0) (conv_refl_l H15)) in H15.

  exists s s' ; intuition ; auto with coc.
  apply tposr_coerce_trans with A' ; auto with coc.
  apply tposr_coerce_trans with A ; auto with coc.
  apply coerce_coerce_env with (A :: e) ; auto with coc.
  apply tposr_coerce_trans with B ; auto with coc.
  apply tposr_coerce_trans with B' ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  
  elim conv_subset_sum with U P A B .
  pose (tposr_eq_conv H1) ; auto with coc.

  elim conv_subset_sum with U' P A' B'.
  pose (tposr_eq_conv H2) ; auto with coc.

  apply IHcoerce_rc_depth ; auto.
  apply tposr_eq_trans with A ; auto with coc.

  apply IHcoerce_rc_depth ; auto.
  apply tposr_eq_trans with C ; auto with coc.
Qed.

Corollary injectivity_of_sum_coerce : forall e A A' B B' s, 
  e |-- Sum_l A B >-> Sum_l A' B' : s ->
  exists2 s1 s2, e |-- A >-> A' : s1 /\ A :: e |-- B >-> B' : s2 /\ sum_sort s1 s2 s.
Proof.
  intros.
  destruct (coerce_coerce_rc_depth H).
  eapply injectivity_of_sum_coerce_rc_depth_aux with (Sum_l A B) (Sum_l A' B') x ; auto.
  apply tposr_eq_tposr ; apply (coerce_refl_l H).
  apply tposr_eq_tposr ; apply (coerce_refl_r H).
Qed.
