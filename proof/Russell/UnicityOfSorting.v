Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import Conv_Dec.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Substitution.
Require Import CCPD.Coercion.
Require Import CCPD.GenerationNotKind.
Require Import CCPD.GenerationCoerce.
Require Import CCPD.Generation.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Lemma unique_range_sort : forall t e T T', e |- t : T -> e |- t : T' -> 
forall s1 s2, 
(type_range T = Srt s1 -> type_range T' = Srt s2 -> s1 = s2)(* /\
(type_dom T = Srt s1 -> type_dom T' = Srt s2 -> s1 = s2)*).
Proof.
  induction t ; simpl ; intros ; 
  auto with coc core arith datatypes ; try discriminate.

  destruct (typ_sort H).
  destruct (typ_sort H0).
  rewrite H4 in H1.
  rewrite H6 in H2.
  simpl in H1, H2.
  inversion H1 ; inversion H2.
  auto.

  (* Var *)
  exact (unique_var_range_sort H H1 H0 H2).
    
  (* Abs *)  
  induction (sort_of_abs_range H H1).
  do 2 destruct H3 ; intuition.
  induction (sort_of_abs_range H0 H2).
  do 2 destruct H6 ; intuition.

  apply (IHt2 _ _ _ H3 H6 s1 s2) ; simpl ; auto.

  (* App goes well *)
  induction (sort_of_app_range H H1).
  destruct H3 ; intuition.
  induction (sort_of_app_range H0 H2).
  destruct H6 ; intuition.

  apply (IHt1 _ _ _ H3 H6) ; simpl ; auto.

  pose (term_type_range_kinded H4 H8).
  rewrite e0 in H3.
  pose (type_no_kind_prod_type2 H3).
  simpl in t.
  intuition.

  induction (sort_of_app_range H0 H2).
  destruct H6 ; intuition.

  apply (IHt1 _ _ _ H3 H6) ; simpl ; auto.

  pose (term_type_range_kinded H4 H5).
  rewrite e0 in H3.
  pose (type_no_kind_prod_type2 H3).
  simpl in t.
  intuition.

  pose (term_type_range_kinded H4 H5).
  rewrite e0 in H3.
  pose (type_no_kind_prod_type2 H3).
  simpl in t.
  intuition.

  (* Pair *)
  induction (sort_of_pair_range H H1).
  do 3 destruct H3 ; intuition.
  induction (sort_of_pair_range H0 H2).
  do 3 destruct H9 ; intuition.

  apply (IHt3 _ _ _ H7 H14) ; simpl ; auto.
  unfold subst ; apply type_range_subst2 ; auto.
  unfold subst ; apply type_range_subst2 ; auto.
  
  (* Prod *)
  induction (generation_prod H).
  induction (generation_prod H0).
  rewrite H3 in H.
  rewrite H4 in H0.
  induction (generation_prod2 H).
  induction (generation_prod2 H0).
  apply (IHt2 _ _ _ H6 H8).
  rewrite <- H3 ; auto.
  rewrite <- H4 ; auto.

  (* Sum *)
  induction (generation_sum H).
  induction (generation_sum H0).
  rewrite H3 in H.
  rewrite H4 in H0.
  induction (generation_sum2 H).
  destruct H5.
  destruct H6.
  induction (generation_sum2 H0).
  destruct H8.
  destruct H9.
  apply (IHt2 _ _ _ H6 H9).
  rewrite <- H3 ; auto.
  rewrite <- H4 ; auto.

  (* Subset *)
  pose (generation_subset H).
  pose (generation_subset H0).
  rewrite e0 in H1.
  rewrite e1 in H2.
  simpl in H1 ; simpl in H2.
  rewrite H2 in H1.
  inversion H1 ; auto.

  (* Pi1 *)
  induction (sort_of_pi1_range H H1).
  do 2 destruct H3 ; intuition.
  induction (sort_of_pi1_range H0 H2).
  do 2 destruct H5 ; intuition.
  
  unfold sum_sort in H6.
  destruct H6.

  unfold sum_sort in H9.
  destruct H9.

  intuition.
  
  apply (IHt _ _ _ H4 H7) ; simpl ; auto.
  rewrite H10.
  rewrite <- H3.
  rewrite H9 ; auto.

  rewrite H11.
  rewrite H6 in H5.
  assumption.

  destruct H8.
  destruct H6.
  rewrite H8.
  rewrite H6 in H3.
  simpl in H3.
  inversion H3 ; auto.

  unfold sum_sort in H9.
  destruct H9.
  
  intuition.

  rewrite H9.
  rewrite H6 in H5.
  simpl in H5.
  inversion H5 ; auto.

  intuition.
  rewrite H6 ; rewrite H9 ; auto.

  (* Pi2 *)
  induction (sort_of_pi2_range H H1).
  do 2 destruct H3 ; intuition.
  induction (sort_of_pi2_range H0 H2).
  do 2 destruct H5 ; intuition.
  
  apply (IHt _ _ _ H4 H7) ; simpl.
  unfold subst in H3 ; induction (type_range_subst _ _ _ H3).
  simpl in H8 ; discriminate.
  assumption.

  unfold subst in H5 ; induction (type_range_subst _ _ _ H5).
  simpl in H8 ; discriminate.
  assumption.

  induction (sort_of_letin_range H H1).
  destruct H3 ; intuition.
  induction (sort_of_letin_range H0 H2).
  destruct H5 ; intuition.

  elim (@not_t_let_in _ _ _ H t1 t2).
  auto.
Qed.

Theorem unique_sort : forall t e s s', 
  e |- t : (Srt s) -> e |- t : (Srt s') -> s = s'.
Proof.
  intros.
  exact (unique_range_sort H H0 (refl_equal (Srt s)) (refl_equal (Srt s'))).
Qed.
  
  