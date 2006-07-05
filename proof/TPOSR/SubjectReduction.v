Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.MyList.

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
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.Coercion.
Require Import Lambda.TPOSR.Equiv.
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.TypesDepth.
Require Import Lambda.TPOSR.TypesFunctionality.
Require Import Lambda.TPOSR.UniquenessOfTypes.
Require Import Lambda.TPOSR.ChurchRosserDepth.
Require Import Lambda.TPOSR.ChurchRosser.
Require Import Lambda.TPOSR.Injectivity.

Set Implicit Arguments.

Theorem subject_reduction_depth : forall t t', par_lred1 t t' -> forall e T, tposr_term_depth e t T ->
  tposr e t t' T.
Proof.
  unfold tposr_term_depth ; induction 1 ; simpl ; intros ; destruct_exists. 

  (* Beta *)
  pose (generation_app_depth H1) ; destruct_exists.
  assert(exists E, tposr_term_depth (T :: e) M E /\ e |-- Prod_l T E >-> Prod_l a Typ : b0).
  assert(e |-- (Prod_l a Typ) -> (Prod_l a Typ) : (Srt_l b0)).
  apply tposr_prod with c ; auto with coc.
  apply (refl_l (fromd H2)).
  apply (coerce_refl_l H4).

  destruct H8 ; destruct_exists.
  pose (generation_lambda_depth H8) ; destruct_exists.
  exists a5.
  split.
  exists a4 ; exists c1 ;auto.
  apply tposr_coerce_sym.
  pose (coerce_refl_l H19).
  rewrite (unique_sort H9 t).
  assumption.
  
  inversion H8.
  exists Typ.
  split.
  exists b2 ; exists c0.
  assumption.
  auto with coc.

  destruct_exists.
  pose (injectivity_of_pi_coerce H10).
  destruct_exists.
  apply tposr_conv with (lsubst N Typ) b0 ; auto with coc.
  pose (IHpar_lred1_1 _ _ H9).
  apply tposr_beta with T x2 Typ b0 ; auto with coc.
  apply (coerce_refl_r H11).
  apply type_coerce_env with (a :: e) ; auto with coc.
  apply (coerce_refl_l H4).
  apply coerce_env_hd with x2 ; auto with coc.
  apply tposr_conv with x1 b0 ; auto with coc.
  apply coerce_coerce_env with (a :: e) ; auto with coc.
  apply coerce_env_hd with x2 ; auto with coc.

  assert(tposr_term_depth e N a).
  exists a1 ; exists  b1 ; auto.
  pose (IHpar_lred1_2 _ _ H13).
  apply tposr_conv with a x2 ; auto with coc.

  (* Pi1 *)
  pose (generation_pi1_depth H0) ; destruct_exists.
  destruct H8 ; destruct_exists.

  generalize dependent e.
  rewrite H5.
  rewrite <- H8.
  rewrite <- H9.
  rewrite H13.
  rewrite H10.
  clear H5 H8 H9 H10 H13 a1 b1 a2.
  intros.
  pose (generation_pair_depth H11) ; destruct_exists.
  generalize dependent e.
  rewrite H5.
  rewrite H19.
  clear H19 H5 ; intros.
  
  pose (injectivity_of_sum_coerce H20) ; destruct_exists.
  pose (unique_sort (coerce_refl_r H5) (fromd H8)).
  pose (unique_sort (coerce_refl_l H19) (fromd H3)).
  assert(a :: e |-- a2 -> b3 : Srt_l c3).
  apply type_coerce_env with (a1 :: e) ; auto with coc.
  apply (fromd H10).
  apply coerce_env_hd with a5 ; auto with coc.

  pose (unique_sort (coerce_refl_r H19) H22).

  apply tposr_equiv_r with a ; auto with coc.
  apply tposr_pi1_red with b1 c2 b3 c3 x2 a4 ; auto with coc.
  apply (fromd H8).
  apply (fromd H10).
  apply tposr_pair with c2 c3 x2 ; auto with coc.
  apply (fromd H8).
  apply (fromd H10).

  assert(tposr_term_depth e M a1).
  exists a3 ; exists b4 ; auto.
  apply (IHpar_lred1 _ _ H23).

  apply (fromd H17).
  
  rewrite <- e0 ; auto.

  rewrite <- e2 ; auto.
  
  pose (generation_pair_depth H11) ; destruct_exists.
  generalize dependent e.
  inversion H8.
  subst.
  inversion H1 ; subst.
  intros.
  clear H1 H8.
  
  assert(tposr_term_depth e a2 a).
  exists a6 ; exists b6 ; auto.
  pose (IHpar_lred1 _ _ H1).

  pose (unique_sort (fromd H15) (coerce_refl_r H9)).
  pose (unique_sort (fromd H5) (fromd H17)).

  apply tposr_equiv_r with a1 ; auto with coc.
  apply tposr_pi1_red with b4 c2 b5 c3 x2 a7 ; auto with coc.
  apply (fromd H15).
  apply (fromd H17).
  apply tposr_pair with c2 c3 x2 ; auto with coc.
  apply (fromd H15).
  apply (fromd H17).

  apply (fromd H22).
  rewrite e0 ; assumption.
  rewrite <- e1 ; assumption.

  (* Pi2 *)
  pose (generation_pi2_depth H0).

Admitted.

Corollary subject_reduction : forall t t', par_lred1 t t' -> forall e T, tposr_term e t T ->
  e |-- t -> t' : T.
Proof.
  intros.
  apply subject_reduction_depth ; eauto with coc ecoc.
Qed.

Corollary subject_reduction_p : forall t t', par_lred t t' -> 
  forall e T, tposr_term e t T ->
  tposrp e t t' T.
Proof.
  induction 1.
  intros.
  apply tposrp_tposr.
  apply (subject_reduction H H0).
  intros.
  pose (IHclos_trans1 _ _ H1).
  pose (tposrp_refl_r t).
  assert(tposr_term e y T).
  exists y ; auto.
  pose (IHclos_trans2 _ _ H2).
  apply tposrp_trans with y ; auto.
Qed.
