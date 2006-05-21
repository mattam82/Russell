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
Require Import CCPD.GenerationRange.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Lemma unique_range_sort : forall t e T T', e |- t : T -> e |- t : T' -> 
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

  (* Let_in *)
  elim (@not_t_let_in _ _ _ H t1 t2).
  auto.
Qed.

Theorem unique_sort : forall t e s s', 
  e |- t : (Srt s) -> e |- t : (Srt s') -> s = s'.
Proof.
  intros.
  exact (unique_range_sort H H0 (refl_equal (Srt s)) (refl_equal (Srt s'))).
Qed.
  
  