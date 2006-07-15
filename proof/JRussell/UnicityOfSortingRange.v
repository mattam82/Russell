Require Import Lambda.Utils.
Require Import Lambda.Tactics.

Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Conv_Dec.
Require Import Lambda.LiftSubst.
Require Import Lambda.InvLiftSubst.
Require Import Lambda.Env.
Require Import Lambda.JRussell.Types.
Require Import Lambda.JRussell.Basic.
Require Import Lambda.JRussell.Thinning.
Require Import Lambda.JRussell.Substitution.
Require Import Lambda.JRussell.Coercion.
Require Import Lambda.JRussell.GenerationNotKind.
Require Import Lambda.JRussell.GenerationCoerce.
Require Import Lambda.JRussell.Generation.
Require Import Lambda.JRussell.GenerationRange.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

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


Lemma generation_prod2 : forall e t T, e |-= t : T ->
  forall U V, t = Prod U V ->
  exists s, T = Srt s /\
  (exists s', e |-= U : Srt s') /\ (U :: e) |-= V : Srt s.
Proof.
  intros e t T H.
  induction H ; simpl ; intros; subst ; try discriminate.

  pose (inv_lift_prod _ _ H1).
  destruct_exists.
  subst.
  destruct (IHtyp1 x x0) ; auto.
  destruct_exists.
  exists x1 ; subst T ; intuition ; auto.
  exists x2.
  change (Srt x2) with (lift 1 (Srt x2)).
  change (lift_rec 1 x 0) with (lift 1 x).
  apply thinning_n with e.
  eauto with coc.
  apply consistent_cons with s ; eauto with coc.
  apply typ_consistent with U (Srt s) ; auto.
  assumption.

  change (Srt x1) with (lift_rec 1 (Srt x1) 1).
  eapply type_weak_weak with e U s (x :: e) ; auto.
  eauto with coc.
  eauto with coc.

  inversion H1 ; subst.
  exists s2 ; intuition.
  exists s1 ; auto.

  destruct (IHtyp U0 V0) ; auto.
  exists x.
  intuition.
  rewrite H2 in H0.
  apply (coerce_propset_l H0).
Qed.

Lemma generation_sum2 : forall e t T, e |-= t : T ->
  forall U V, t = Sum U V ->
  exists3 s1 s2 s3, T = Srt s3 /\
  e |-= U : Srt s1 /\ (U :: e) |-= V : Srt s2 /\ sum_sort s1 s2 s3.
Proof.
  intros e t T H.
  induction H ; simpl ; intros; subst ; try discriminate.

  pose (inv_lift_sum _ _ H1).
  destruct_exists.
  subst.
  destruct (IHtyp1 x x0) ; auto.
  destruct_exists.
  exists a b c ; subst T ; intuition ; auto.
  change (Srt a) with (lift 1 (Srt a)).
  change (lift_rec 1 x 0) with (lift 1 x).
  apply thinning_n with e.
  eauto with coc.
  apply consistent_cons with s ; eauto with coc.
  apply typ_consistent with U (Srt s) ; auto.
  assumption.

  change (Srt b) with (lift_rec 1 (Srt b) 1).
  eapply type_weak_weak with e U s (x :: e) ; auto.
  eauto with coc.
  eauto with coc.

  inversion H2 ; subst.
  exists s1 s2 s3 ; intuition.

  destruct (IHtyp U0 V0) ; auto.
  intuition.
  exists a b c.
  intuition.
  subst U.
  apply (coerce_propset_l H0).
Qed.

Lemma generation_subset : forall e t T, e |-= t : T ->
  forall U V, t = Subset U V ->
  T = Srt set /\
  e |-= U : Srt set /\ (U :: e) |-= V : Srt prop.
Proof.
  intros e t T H.
  induction H ; simpl ; intros; subst ; try discriminate.

  pose (inv_lift_subset _ _ H1).
  destruct_exists.
  subst.
  destruct (IHtyp1 x x0) ; auto.
  destruct_exists.
  subst T ; intuition ; auto.
  change (Srt set) with (lift 1 (Srt set)).
  change (lift_rec 1 x 0) with (lift 1 x).
  apply thinning_n with e.
  eauto with coc.
  apply consistent_cons with s ; eauto with coc.
  apply typ_consistent with U (Srt s) ; auto.
  assumption.

  change (Srt prop) with (lift_rec 1 (Srt prop) 1).
  eapply type_weak_weak with e U s (x :: e) ; auto.
  eauto with coc.
  eauto with coc.

  inversion H1 ; subst.
  intuition.

  destruct (IHtyp U0 V0) ; auto.
  intuition.
  intuition.
  subst U.
  apply (coerce_propset_l H0).
Qed.

Lemma unique_range_sort : forall t e T T', e |-= t : T -> e |-= t : T' -> 
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
  pose (generation_prod2 H (refl_equal (Prod t1 t2))).
  pose (generation_prod2 H0 (refl_equal (Prod t1 t2))).
  destruct_exists ; intuition.
  rewrite H3 in H2 ; auto.
  rewrite H4 in H1 ; auto.
  apply (IHt2 _ _ _ H8 H6) ; auto.

  (* Sum *)
  pose (generation_sum2 H (refl_equal (Sum t1 t2))).
  pose (generation_sum2 H0 (refl_equal (Sum t1 t2))).
  destruct_exists ; intuition.
  rewrite H3 in H2 ; auto.
  rewrite H4 in H1 ; auto.
  assert(a0 = a).
  apply (IHt1 _ _ _ H8 H5 a0 a) ; auto.
  assert(b0 = b).
  apply (IHt2 _ _ _ H9 H6 b0 b) ; auto.
  subst.
  assert(Heq:=sum_sort_functional H7 H10).
  subst ; auto.
  inversion H1 ; inversion H2.
  subst ; auto.

  (* Subset *)
  pose (generation_subset H (refl_equal (Subset t1 t2))).
  pose (generation_subset H0 (refl_equal (Subset t1 t2))).
  destruct_exists ; intuition.
  subst T ; subst T'.
  simpl in H1 ; simpl in H2.
  rewrite H2 in H1.
  inversion H1 ; auto.

  (* Pi1 *)
  induction (sort_of_pi1_range H H1).

  (* Pi2 *)
  induction (sort_of_pi2_range H H1).
Qed.

