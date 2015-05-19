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
Require Import Lambda.TPOSR.Equiv.
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.TypesDepth.
Require Import Lambda.TPOSR.TypesFunctionality.

Set Implicit Arguments.

Lemma sum_sort_functional : forall a b c c', sum_sort a b c -> sum_sort a b c' -> c = c'.
Proof.
  intros.
  destruct H ; destruct H0 ; intuition.

  rewrite H4 ; rewrite H5 ; auto.

  rewrite H1 in H ; discriminate.

  rewrite H1 in H ; discriminate.
  
  rewrite H4 ; rewrite H5 ; auto.
Qed.

Lemma toq : forall G M M' A n, G |-- M -> M' : A [n] -> tposr_term_depth G M A.
Proof.
  intros ; exists M' ; exists n ; auto.
Qed.

Theorem uniqueness_of_types : forall e M A B, 
  tposr_term_depth e M A -> tposr_term_depth e M B -> equiv e A B.
Proof. 
  intros e M ; generalize e ; clear e.
  induction M ; unfold tposr_term_depth, tposr_term ; simpl ; intros ; destruct_exists ; auto with coc.

  (* Sorts *)
  pose (tposrd_tposr_type H).
  pose (tposrd_tposr_type H0).
  pose (generation_sort t).
  pose (generation_sort t0).
  destruct_exists.
  rewrite H4 ; rewrite H2 ; unfold equiv ; intuition.

  (* Var *)
  pose (tposrd_tposr_type H).
  pose (tposrd_tposr_type H0).
  pose (generation_var t).
  pose (generation_var t0).
  destruct_exists.
  destruct H5.
  destruct H2.
  pose (fun_item _ _ _ _ _ H7 H8).
  rewrite e0 in H5.
  rewrite <- H2 in H5.
  rewrite H5 in H6.
  rewrite (unique_sort (coerce_refl_r H3) (coerce_refl_r H6)) in H3.
  right ; exists x6 ; apply tposr_coerce_trans with x3 ; auto with coc.


  (* Abs *)
  pose (generation_lambda_depth H) ; destruct_exists.
  pose (generation_lambda_depth H0) ; destruct_exists.
  pose (IHM2 _ _ _ (toq H3) (toq H11)).
  pose (tposrd_unique_sort H1 H9).
  destruct e0.
  destruct H17.
  rewrite H18 in H13.
  elim (tposr_not_kind (fromd H13)).
  right.
  exists b0.
  assert(tposr_eq e M1 M1 b2).
  apply tposr_eq_tposr.
  apply (refl_l (fromd H9)).
  destruct H17.
  assert(b0 = x3).
  apply (unique_sort (fromd H5) (coerce_refl_l H17)).

  apply tposr_coerce_trans with (Prod_l M1 a1) ; auto with coc.
  assert(tposr_coerce e (Prod_l M1 a1) (Prod_l M1 a4) b0).
  rewrite <- H19 in H17.
  apply tposr_coerce_prod with b2 ; auto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  rewrite <- (unique_sort (fromd H13) (coerce_refl_r H17)).
  eauto with coc ecoc.

  apply tposr_coerce_trans with (Prod_l M1 a4) ; auto.
  rewrite H19.
  rewrite <- (unique_sort (fromd H13) (coerce_refl_r H17)).
  apply tposr_coerce_sym.
  apply H16.
  
  (* App *)
  pose (generation_app_depth H) ; destruct_exists.
  pose (generation_app_depth H0) ; destruct_exists.
  pose (equiv_sort_trans H6 H13).
  right.
  exists b0 ; auto.

  (* Pair *)
  pose (generation_pair_depth H0) ; destruct_exists.
  pose (generation_pair_depth H) ; destruct_exists.
  rewrite H13 in H1.
  rewrite H1 in H24.
  right ; exists x4.
  apply (equiv_sort_trans H24 H12).

  (* Prod *)
  pose (generation_prod_depth H) ; destruct_exists.
  pose (generation_prod_depth H0) ; destruct_exists.
  pose (tposrd_unique_sort H9 H3).
  rewrite e0 in H12.
  apply (equiv_trans H6 H12).

  (* Sum *)
  pose (generation_sum_depth H) ; destruct_exists.
  pose (generation_sum_depth H0) ; destruct_exists.
  pose (tposrd_unique_sort H8 H1).
  pose (tposrd_unique_sort H10 H3).
  rewrite e1 in H12.
  rewrite e0 in H12.
  pose (sum_sort_functional H5 H12).
  rewrite <- e2 in H14.
  apply (equiv_trans H7 H14).

  (* Subset *)
  pose (generation_subset_depth H) ; destruct_exists.
  pose (generation_subset_depth H0) ; destruct_exists.
  right ; exists kind ; apply (equiv_sort_trans H6 H12).

  (* Pi1 *)
  pose (generation_pi1_depth H) ; destruct_exists.
  pose (generation_pi1_depth H0) ; destruct_exists.
  subst.
  inversion H6 ; subst.
  apply (equiv_trans H2 H7).

  (* Pi2 *)
  pose (generation_pi2_depth H) ; destruct_exists.
  pose (generation_pi2_depth H0) ; destruct_exists.
  subst.
  inversion H6 ; subst.
  apply (equiv_trans H2 H7).
Qed.

Corollary tposr_uniqueness_of_types : forall e M M' M'' A B, 
  e |-- M -> M' : A -> e |-- M -> M'' : B -> equiv e A B.
Proof. 
  intros.
  pose (tposr_tposrd_type H).
  pose (tposr_tposrd_type H0).
  destruct_exists.
  apply (uniqueness_of_types (toq H2) (toq H1)).
Qed. 

Corollary tposrp_uniqueness_of_types : forall e M M' M'' A B, 
  e |-- M -+> M' : A -> e |-- M -+> M'' : B -> equiv e A B.
Proof. 
  intros.
  pose (tposrp_refl_l H).
  pose (tposrp_refl_l H0).
  pose (tposr_tposrd_type t).
  pose (tposr_tposrd_type t0).
  destruct_exists.
  apply (uniqueness_of_types (toq H2) (toq H1)).
Qed. 

