Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.MyList.

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
Require Import TPOSR.TypesFunctionality.

Require Import Meta.TPOSR_Russell.

Set Implicit Arguments.

Definition tposr_term G M A := exists M', exists n, G |-- M -> M' : A [n].

Lemma sum_sort_functional : forall a b c c', sum_sort a b c -> sum_sort a b c' -> c = c'.
Proof.
  intros.
  destruct H ; destruct H0 ; intuition.

  rewrite H4 ; rewrite H5 ; auto.

  rewrite H1 in H ; discriminate.

  rewrite H1 in H ; discriminate.
  
  rewrite H4 ; rewrite H5 ; auto.
Qed.

Lemma toq : forall G M M' A n, G |-- M -> M' : A [n] -> tposr_term G M A.
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

  left ; rewrite H0 ; rewrite H ; reflexivity.
  
  right ; exists x ; rewrite H ; auto with coc.

  right ; exists x ; rewrite H0 ; auto with coc.

  pose (tposr_eq_unique_sort_right H H0).
  rewrite e in H.
  right ; exists x ; apply tposr_eq_trans with C ; auto with coc.
Qed.

Theorem uniqueness_of_types : forall e M A B, 
  tposr_term e M A -> tposr_term e M B -> equiv e A B.
Proof. 
  intros e M ; generalize e ; clear e.
  induction M ; unfold tposr_term ; simpl ; intros ; destruct_exists ; auto with coc.

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
  destruct H3 ; destruct_exists.
  rewrite H3 ; assumption.
  destruct H6 ; destruct_exists.
  rewrite <- H6 in H3.
  right ; exists x7 ; auto with coc.
  right ; exists x7.
  apply tposr_eq_trans with x3 ; auto with coc.
  rewrite (tposr_eq_unique_sort_right H3 H6).
  assumption.

  (* Abs *)
  pose (generation_lambda H) ; destruct_exists.
  pose (generation_lambda H0) ; destruct_exists.
  pose (IHM2 _ _ _ (toq H3) (toq H11)).
  pose (tposrd_unique_sort H1 H9).
  destruct e0.
  rewrite H17 in H8.
  apply (equiv_trans H8 H16).
   
  assert(tposr_eq e M1 M1 b2).
  apply tposr_eq_tposr.
  apply left_refl with a2 ; auto.
  apply tposrd_tposr_type with c2 ; auto.

  destruct H8 ; destruct_exists.

  rewrite H8 ; right ; intuition.

  destruct H16 ; destruct_exists.
  rewrite H16.
  exists x3.
  apply pi_functionality with b2 ; auto with coc.

  exists x3.
  apply tposr_eq_trans with (Prod_l M1 a4) ; auto with coc.
  apply pi_functionality with b2 ; auto with coc.

  pose (pi_functionality H18 H17).
  rewrite <- (tposr_eq_unique_sort_right H16 t) ; auto with coc.

  pose (pi_functionality H18 H17).
  destruct H16 ; destruct_exists.
  rewrite H16.
  right ; exists x3.
  rewrite (tposr_eq_unique_sort (tposr_eq_sym H8) t) in H8 ; auto with coc.
  apply tposr_eq_trans with (Prod_l M1 a1) ; auto with coc.

  right ; exists x3.
  rewrite (tposr_eq_unique_sort (tposr_eq_sym H8) t) in H8 ; auto with coc.
  rewrite (tposr_eq_unique_sort_right H16 t) in H16 ; auto with coc.
  apply tposr_eq_trans with (Prod_l M1 a1) ; auto with coc.
  apply tposr_eq_trans with (Prod_l M1 a4) ; auto with coc.

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
  apply (equiv_trans H24 H12).

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
  apply (equiv_trans H6 H12).

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