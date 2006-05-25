Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Conv_Dec.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Russell.Types.
Require Import Russell.Thinning.
Require Import Russell.Substitution.
Require Import Russell.Coercion.
Require Import Russell.GenerationNotKind.
Require Import Russell.GenerationCoerce.
Require Import Russell.Generation.
Require Import Russell.GenerationRange.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Lemma unique_range_sort : forall t e T T', e |-- t : T -> e |-- t : T' -> 
forall s1 s2, 
(type_range T = Srt s1 -> type_range T' = Srt s2 -> s1 = s2).
Proof.
  induction t ; simpl ; intros ; 
  auto with coc core arith datatypes ; try discriminate.

  destruct (typ_sort H).
  destruct (typ_sort H0).
  rewrite H4 in H1.
  rewrite H6 in H2.
  simpl in H1, H2.
  inversion H1 ; inversion H2 ; auto.

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
  pose (type_no_kind_prod_type H3).
  simpl in t.
  intuition.

  induction (sort_of_app_range H0 H2).
  destruct H6 ; intuition.

  apply (IHt1 _ _ _ H3 H6) ; simpl ; auto.

  pose (term_type_range_kinded H4 H5).
  rewrite e0 in H3.
  pose (type_no_kind_prod_type H3).
  simpl in t.
  intuition.

  pose (term_type_range_kinded H4 H5).
  rewrite e0 in H3.
  pose (type_no_kind_prod_type H3).
  simpl in t.
  intuition.

  (* Pair *)
  induction (sort_of_pair_range H H1).
  
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
  induction (generation_sum2 H0).
  destruct H6.
  destruct H8.
  apply (IHt2 _ _ _ H6 H8).

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

  (* Pi2 *)
  induction (sort_of_pi2_range H H1).
Qed.

