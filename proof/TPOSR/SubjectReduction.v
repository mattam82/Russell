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
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.TypesDepth.
Require Import Lambda.TPOSR.TypesFunctionality.
Require Import Lambda.TPOSR.UniquenessOfTypes.
Require Import Lambda.TPOSR.ChurchRosserDepth.
Require Import Lambda.TPOSR.ChurchRosser.

Require Import Lambda.Meta.TPOSR_Russell.

Set Implicit Arguments.

Theorem subject_reduction : forall t t', par_lred1 t t' -> forall e T, tposr_term_depth e t T ->
  tposr e t t' T.
Proof.
  unfold tposr_term_depth ; induction 1 ; simpl ; intros ; destruct_exists. 

  (* Beta *)
  pose (generation_app H1) ; destruct_exists.
  assert(exists E, tposr_term_depth (T :: e) M E /\ e |-- Prod_l T E ~= Prod_l a Typ : b0).
  assert(e |-- (Prod_l a Typ) -> (Prod_l a Typ) : (Srt_l b0)).
  apply tposr_prod with c ; auto with coc.
  apply (left_refl (fromd H2)).
  apply (left_refl (fromd H4)).

  destruct H9 ; destruct_exists.
  pose (generation_lambda H9) ; destruct_exists.
  exists a5.
  split.
  exists a4 ; exists c2 ;auto.
  apply tposr_eq_sym.
  apply equiv_eq ; auto with coc.
  right ; exists b4 ; auto.

  inversion H9.
  exists Typ.
  split.
  exists b2 ; exists c1.
  assumption.
  apply tposr_eq_tposr.
  assumption.

  destruct_exists.
  pose (injectivity_of_pi H11).
  destruct_exists.
  apply tposr_conv_r with (lsubst N Typ) b0 ; auto with coc.
  pose (IHpar_lred1_1 _ _ H10).
  apply tposr_beta with T x2 a0 b0 ; auto with coc.
  destruct (conv_refls H12).
  apply H14.
  apply conv_env with (a :: e) ; auto with coc.
  apply (fromd H4).
  apply conv_env_hd with x2 ; auto with coc.
  apply tposr_conv_l with x1 b0 ; auto with coc.

  assert(tposr_term_depth e N a).
  exists a1 ; exists  b1 ; auto.
  pose (IHpar_lred1_2 _ _ H14).
  apply tposr_conv_l with a x2 ; auto with coc.

  (* Pi1 *)
  pose (generation_pi1 H0) ; destruct_exists.
  destruct H8 ; destruct_exists.

  generalize dependent e.
  rewrite H5.
  rewrite <- H8.
  rewrite <- H9.
  rewrite H13.
  rewrite H10.
  clear H5 H8 H9 H10 H13 a1 b1 a2.
  intros.
  pose (generation_pair H11) ; destruct_exists.
  generalize dependent e.
  rewrite H5.
  rewrite H19.
  clear H19 H5 ; intros.
  
  pose (injectivity_of_sum H20) ; destruct_exists.
  pose (tposr_unique_sort (conv_refl_r H5) (fromd H8)).
  pose (tposr_unique_sort (conv_refl_l H19) (fromd H3)).
  assert(a :: e |-- a2 -> b3 : Srt_l c3).
  apply conv_env with (a1 :: e) ; auto with coc.
  apply (fromd H10).
  apply conv_env_hd with a5 ; auto with coc.

  pose (tposr_unique_sort (conv_refl_r H19) H22).


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
  
  pose (generation_pair H11) ; destruct_exists.
  generalize dependent e.
  inversion H8.
  subst.
  inversion H1 ; subst.
  intros.
  clear H1 H8.
  
  assert(tposr_term_depth e a2 a).
  exists a6 ; exists b6 ; auto.
  pose (IHpar_lred1 _ _ H1).

  pose (tposr_unique_sort (fromd H15) (conv_refl_r H9)).
  pose (tposr_unique_sort (fromd H5) (fromd H17)).

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
  pose (generation_pi2 H0).

Admitted.



