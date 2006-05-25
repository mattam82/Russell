Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import TPOSR.Terms.
Require Import TPOSR.Reduction.
Require Import TPOSR.Conv.
Require Import TPOSR.LiftSubst.
Require Import TPOSR.Env.
Require Import TPOSR.Types.
Require Import TPOSR.Basic.
Require Import TPOSR.Thinning.
Require Import TPOSR.LeftReflexivity.
Require Import TPOSR.Substitution.
Require Import TPOSR.CtxConversion.
Require Import TPOSR.RightReflexivity.
Require Import TPOSR.Generation.
Require Import TPOSR.TypesDepth.

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
  destruct H4.
  right ; exists x2 x1.
  rewrite H4 ; assumption.
  destruct_exists.
  destruct (conv_refls H4).
  right ; exists T x3 ; assumption.
  
  right.
  pose (generation_lambda H0) ; destruct_exists.
  pose (H _ H2 _ _ _ _  H1).
  pose (H _ H4 _ _ _ _ H3).
  induction H8.
  rewrite H8.
  exists (Prod_l a b1) b0.
  apply tposr_prod with b ; auto with coc.
  apply tposrd_tposr_type with c ; auto with coc.
  apply tposrd_tposr_type with c1 ; auto with coc.
  destruct_exists.
  exists T x0 ; auto with coc.
  destruct (conv_refls H8) ; auto.

  pose (generation_app H0) ; destruct_exists.
  destruct H7.
  right ; exists Y s ; assumption.
  destruct (conv_refls H7).
  right ; exists Y s ; auto.
  destruct (conv_refls H7_).
  right ; exists W s ; auto.

  pose (generation_pair H0) ; destruct_exists.
  destruct H12.
  right.
  assert(e |-- Sum_l a a0 -> Sum_l b b0 : Srt_l x0) ; auto with coc.
  apply tposr_sum with c c0 ; auto.
  apply tposrd_tposr_type with d ; auto.
  apply tposrd_tposr_type with d0 ; auto.
  exists (Sum_l b b0) x0.
  rewrite H12 ; assumption.
  destruct_exists.
  right ; exists T x1.
  destruct (conv_refls H12) ; assumption.

  pose (generation_prod H0) ; destruct_exists.
  destruct H6 ; destruct_exists.
  left ; exists b0 ; auto.
  destruct (conv_refls H6).
  right ; exists T x0 ; auto.
  
  pose (generation_sum H0) ; destruct_exists.
  destruct H7 ; destruct_exists.
  left ; exists x0 ; auto.
  destruct (conv_refls H7).
  right ; exists T x1 ; auto.

  pose (generation_subset H0) ; destruct_exists.
  destruct H6 ; destruct_exists.
  left ; exists set ; auto.
  destruct (conv_refls H6).
  right ; exists T x0 ; auto.

  pose (generation_pi1 H0) ; destruct_exists.
  destruct H6 ; destruct_exists.
  right.
  exists b c.
  rewrite H6.
  apply tposrd_tposr_type with d ; auto.
  right ; exists T x1.
  destruct (conv_refls H6) ; assumption.

  pose (generation_pi2 H0) ; destruct_exists.
  destruct H6 ; destruct_exists.
  right.
  exists (lsubst (Pi1_l t) b0) c0.
  rewrite H6.
  change (Srt_l c0) with (lsubst (Pi1_l t) (Srt_l c0)).
  apply substitution with a ; auto with coc.
  apply tposrd_tposr_type with d0 ; auto.
  apply tposr_pi1 with b c a0 b0 c0 x0 ; auto with coc.
  apply tposrd_tposr_type with d ; auto.
  apply tposrd_tposr_type with d0 ; auto.
  pose (tposrd_tposr_type H1) ; auto.
  pose (tposrd_tposr_type H3) ; auto.
  destruct H7 ; destruct_exists.
  pose (tposrd_tposr_type H7) ; auto.
  apply left_refl with a1 ; auto.
  rewrite H7.
  pose (tposrd_tposr_type H8) ; auto.
  pose (tposrd_tposr_type H10) ; auto.
  apply tposr_pair with c c0 x0 ; auto with coc.
  apply left_refl with b ; auto.
  apply left_refl with b0 ; auto.
  apply left_refl with b1 ; auto.
  apply left_refl with b2 ; auto.
  
  right ; exists T x1.
  destruct (conv_refls H6) ; assumption.
Qed.
