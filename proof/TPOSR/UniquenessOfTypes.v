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

Require Import Lambda.Meta.TPOSR_Russell.

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

Lemma tposrd_unique_sort : forall G M M' M'' s s' n m, G |-- M -> M' : Srt_l s [n] ->
  G |-- M -> M'' : Srt_l s' [m] -> s = s'.
Proof.
  intros.
  pose (tposrd_tposr_type H).
  pose (tposrd_tposr_type H0).
  apply (tposr_unique_sort t t0).
Qed.

Lemma tposr_unique_sort_right : forall G A B C s s', G |-- A -> C : Srt_l s ->
  G |-- B -> C : Srt_l s' -> s = s'.
Proof.
  intros.
  pose (right_refl H).
  pose (right_refl H0).
  apply tposr_unique_sort with G C C C ; auto with coc.
Qed.

Lemma tposr_eq_unique_sort_right : forall G A B C s s', G |-- A ~= C : s ->
  G |-- B ~= C : s' -> s = s'.
Proof.
  intros.
  apply tposr_eq_unique_sort with G C A B ; auto with coc.
Qed.

Lemma equiv_sort_trans : forall G A B C s s', equiv_sort G A C s -> equiv_sort G B C s' -> equiv_sort G A B s.
Proof.
  unfold equiv_sort.
  intros.
  pose (tposr_eq_unique_sort_right H H0).
  rewrite <- e in H0.
  apply tposr_eq_trans with C ; auto with coc.
Qed.

Lemma equiv_trans : forall G A B C, equiv G A C -> equiv G B C -> equiv G A B.
Proof.
  unfold equiv.
  intros.
  destruct H ; destruct H0 ; intuition ; destruct_exists.

  destruct H ; destruct H0.
  rewrite H ; rewrite H0 ; left ; unfold eq_kind ; intuition. 
  
  destruct H.
  rewrite H1 in H0.
  pose (conv_refl_r H0).
  elim (tposr_not_kind t) ; auto.

  destruct H0.
  rewrite H1 in H.
  elim (tposr_not_kind (conv_refl_r H)).

  right.

  pose (tposr_eq_unique_sort_right H H0).
  exists x.
  apply tposr_eq_trans with C ; auto with coc.
  rewrite <- e ; auto.
Qed.


Definition tod := tposr_tposrd_type.
Definition fromd := tposrd_tposr_type.

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
  apply (equiv_trans H6 H3).


  (* Abs *)
  pose (generation_lambda H) ; destruct_exists.
  pose (generation_lambda H0) ; destruct_exists.
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
  apply (left_refl (fromd H9)).
  destruct H17.
  assert(b0 = x3).
  apply (tposr_unique_sort (fromd H5) (conv_refl_l H17)).

  apply tposr_eq_trans with (Prod_l M1 a1) ; auto with coc.
  assert(tposr_eq e (Prod_l M1 a1) (Prod_l M1 a4) b0).
  rewrite <- H19 in H17.
  apply (pi_functionality H18 H17).
  assert(b3 = x3).
  apply (tposr_unique_sort (fromd H13) (conv_refl_r H17)).
  apply tposr_eq_trans with (Prod_l M1 a4) ; auto.
  apply tposr_eq_sym.
  rewrite H19.
  rewrite <- H21.
  apply H16.

  (* App *)
  pose (generation_app H) ; destruct_exists.
  pose (generation_app H0) ; destruct_exists.
  pose (equiv_sort_trans H7 H15).
  right.
  exists b0 ; auto.

  (* Pair *)
  pose (generation_pair H0) ; destruct_exists.
  pose (generation_pair H) ; destruct_exists.
  rewrite H13 in H1.
  rewrite H1 in H24.
  right ; exists x4.
  apply (equiv_sort_trans H24 H12).

  (* Prod *)
  pose (generation_prod H) ; destruct_exists.
  pose (generation_prod H0) ; destruct_exists.
  pose (tposrd_unique_sort H9 H3).
  rewrite e0 in H12.
  apply (equiv_trans H6 H12).

  (* Sum *)
  pose (generation_sum H) ; destruct_exists.
  pose (generation_sum H0) ; destruct_exists.
  pose (tposrd_unique_sort H8 H1).
  pose (tposrd_unique_sort H10 H3).
  rewrite e1 in H12.
  rewrite e0 in H12.
  pose (sum_sort_functional H5 H12).
  rewrite <- e2 in H14.
  apply (equiv_trans H7 H14).

  (* Subset *)
  pose (generation_subset H) ; destruct_exists.
  pose (generation_subset H0) ; destruct_exists.
  right ; exists kind ; apply (equiv_sort_trans H6 H12).

  (* Pi1 *)
  pose (generation_pi1 H) ; destruct_exists.
  pose (generation_pi1 H0) ; destruct_exists.
  rewrite H5 in H13.
  inversion H13.
  rewrite <- H18 in H15.
  apply (equiv_trans H7 H15).

  (* Pi2 *)
  pose (generation_pi2 H) ; destruct_exists.
  pose (generation_pi2 H0) ; destruct_exists.
  rewrite H13 in H5.
  inversion H5.
  rewrite H19 in H15.
  apply (equiv_trans H7 H15).
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
