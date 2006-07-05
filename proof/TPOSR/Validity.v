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
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.CtxConversion.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.Equiv.
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.TypesDepth.

Set Implicit Arguments.

Theorem ind_validity : forall n,
  forall e t u T, e |-- t -> u : T [n] -> 
  (exists s, T = Srt_l s) \/
  (exists2 T' s, e |-- T -> T' : Srt_l s).
Proof. 
  intros n.
  apply wf_lt_induction_type with 
  (P := fun n : nat =>
  forall e t u T, e |-- t -> u : T [n] -> 
  (exists s, T = Srt_l s) \/
  (exists2 T' s, e |-- T -> T' : Srt_l s)) ; simpl ; intros.

  destruct t ; simpl ; intros ; auto with coc.

  apply tposr_to_tposrd with e (Srt_l s) u T x ; auto ; intros.
  pose (generation_sort H1).
  left ; exists kind ; intuition.

  apply tposr_to_tposrd with e (Ref_l n0) u T x ; auto ; intros.
  pose (generation_var H1).
  intuition ; destruct_exists.
  pose (wf_tposr H1).
  pose (wf_sort_lift t H3).
  destruct_exists.
  destruct H4 ; destruct_exists.
  elim (eq_kind_typ_r_l H4 H5).

  right ; exists T x3 ; apply (coerce_refl_l H4).  

  right.
  pose (generation_lambda_depth H0) ; destruct_exists.
  exists T b0.
  apply (coerce_refl_l H8).

  pose (generation_app_depth H0) ; destruct_exists.
  right ; exists T b0 ; apply (coerce_refl_l H6).

  pose (generation_pair_depth H0) ; destruct_exists.
  right ; exists T x0 ; apply (coerce_refl_l H12).

  pose (generation_prod_depth H0) ; destruct_exists.
  destruct H6 ; destruct_exists.
  left ; exists b0 ; auto.
  destruct H6.
  rewrite H6 ; rewrite <- H7 ; auto.
  right ; exists T x0 ; apply (coerce_refl_l H6).
  
  pose (generation_sum_depth H0) ; destruct_exists.
  destruct H7 ; destruct_exists.
  left ; exists x0 ; auto.
  destruct H7.
  rewrite H7 ; rewrite <- H8 ; auto.

  right ; exists T x1 ; apply (coerce_refl_l H7).

  pose (generation_subset_depth H0) ; destruct_exists.
  right ; exists T kind ; apply (coerce_refl_l H6).

  pose (generation_pi1_depth H0) ; destruct_exists.
  destruct H7 ; destruct_exists.
  destruct H7.
  left ; exists kind ; auto.
  right ; exists T x1 ; apply (coerce_refl_l H7).

  pose (generation_pi2_depth H0) ; destruct_exists.
  destruct H7 ; destruct_exists.
  destruct H7.
  left ; exists kind ; auto.
  right ; exists T x1 ; apply (coerce_refl_l H7).
Qed.

Corollary validity : forall e t u T, e |-- t -> u : T -> 
  (exists s, T = Srt_l s) \/
  (exists2 T' s, e |-- T -> T' : Srt_l s).
Proof.
  intros.
  pose (tod H) ; destruct_exists.
  apply (ind_validity H0).
Qed.

Corollary validity_tposrp : forall e t u T, e |-- t -+> u : T -> 
  (exists s, T = Srt_l s) \/
  (exists2 T' s, e |-- T -> T' : Srt_l s).
Proof.
  intros.
  pose (tposrp_refl_l H).
  apply (validity t0).
Qed.
