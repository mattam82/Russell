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

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Lemma wf_is_sorted : forall e, wf e ->
  forall x n, item _ x e n -> forall s, x = Srt s -> is_prop s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  elim (inv_nth_nl _ _ _ H).
  pose (item_trunc).
  induction (item_trunc _ _ _ _ H0).

  pose (wf_sort).
  pose (wf_var H).
  induction (wf_sort  H2 w H0).
  rewrite H1 in H3.
  pose (typ_sort H3).
  intuition.
Qed.


Lemma inv_lift_sort : forall t s n, lift n t = Srt s -> t = Srt s.
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
auto.
Qed.

Lemma inv_subst_sort : forall t t' n s, subst_rec t t' n = Srt s -> 
  t = Srt s \/ t' = Srt s.
Proof.
  induction t' ;  simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  generalize H.
  elim (lt_eq_lt_dec n0 n).
  intros a ; case a ; clear a ; intros ; try discriminate ; auto.
  left.
  exact (inv_lift_sort _ _ H0).

  intros.
  discriminate.
Qed.

Lemma gen_sorting_var_aux : forall e t T, e |- t : T ->
  forall n, t = Ref n -> 
  forall s, T = (Srt s) ->
  is_prop s.
Proof.
  induction 1 using typ_wf_mut with
   (P := fun e t T => fun H : e |- t : T =>
   forall n, t = Ref n -> 
   forall s, T = (Srt s) ->
   is_prop s)
   (P0 := fun e => fun H : wf e =>
   forall s, forall n, item _ (Srt s) e n -> is_prop s)
 ; try (simpl ; intros ; try discriminate ; auto with coc).
 
  rewrite H0 in i.
  destruct i.
  rewrite (inv_lift_sort x (S n) (sym_eq H1)) in H2.
  apply (IHtyp s n).
  auto.
 
  rewrite H3 in H0.
  pose (typ_sort H0).
  intuition.
 
  elim (inv_nth_nl _ _ _ H).

  pose (wf_is_sorted).
  apply wf_is_sorted with (T :: e) (Srt s0) n ; auto with coc.
  eapply wf_var with s ; auto with coc.
Qed.

Lemma gen_sorting_var : 
  forall e n s, e |- Ref n : Srt s -> is_prop s.
Proof.
  intros.
  apply gen_sorting_var_aux with e (Ref n) (Srt s) n ; auto.
Qed.

Lemma gen_sorting_app_aux : forall e t Ts, e |- t : Ts ->
  forall M N, t = App M N ->
  forall s, Ts = Srt s -> is_prop s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  inversion_clear H1.
  pose (type_no_kind_prod_type H0).
  induction s ; unfold is_prop ; simpl ; auto.
  pose (subst_to_sort _ H2 (typ_not_kind H)).
  rewrite e0 in t.
  simpl in t ; intuition ; contradiction.

  rewrite H4 in H0.
  pose (typ_sort H0).
  intuition.
Qed.

Lemma gen_sorting_app : forall e M N s, e |- App M N : Srt s -> is_prop s.
Proof.
  intros.
  eapply gen_sorting_app_aux with e (App M N) (Srt s) M N ; auto ; auto.
Qed.

Lemma gen_sorting_pi1_aux : forall e t Ts, e |- t : Ts ->
  forall M, t = Pi1 M ->
  forall s, Ts = Srt s -> is_prop s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  inversion H0.
  pose (type_no_kind_sum_type H).
  induction s ; unfold is_prop ; simpl ; auto.
  rewrite H1 in t0.
  simpl in t0 ; intuition ; contradiction.

  rewrite H4 in H0.
  pose (typ_sort H0).
  intuition.
Qed.

Lemma gen_sorting_pi1 : forall e M s, e |- Pi1 M : Srt s -> is_prop s.
Proof.
  intros.
  eapply gen_sorting_pi1_aux with e (Pi1 M) (Srt s) M ; auto ; auto.
Qed.

Lemma gen_sorting_pi2_aux : forall e t Ts, e |- t : Ts ->
  forall M, t = Pi2 M ->
  forall s, Ts = Srt s -> is_prop s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  inversion H0.
  pose (type_no_kind_sum_type H).
  assert(Pi1 t <> Srt s) ; try (red ; intros ; discriminate).
  pose (subst_to_sort _ H1 H2).
  induction s ; unfold is_prop ; simpl ; auto.
  rewrite e0 in t0.
  simpl in t0 ; intuition ; contradiction.

  rewrite H4 in H0.
  pose (typ_sort H0).
  intuition.
Qed.

Lemma gen_sorting_pi2 : forall e M s, e |- Pi2 M : Srt s -> is_prop s.
Proof.
  intros.
  eapply gen_sorting_pi2_aux with e (Pi2 M) (Srt s) M ; auto ; auto.
Qed.

Lemma sorting_lambda_aux : forall e t Ts, e |- t : Ts ->
  forall T M, t = Abs T M -> forall s, Ts <> Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  unfold not ; intros.
  rewrite H4 in H0.
  destruct (typ_sort H0).
  inversion H6.
  rewrite H8 in H2.
  rewrite H4 in H2.
  pose (coerce_propset_r H2).
  pose (IHtyp1 T M H3 s0).
  contradiction.
Qed.

Lemma sorting_lambda : forall e T M s, ~ e |- Abs T M : Srt s.
Proof.
  unfold not ; intros.
  apply (sorting_lambda_aux H (refl_equal (Abs T M)) (refl_equal (Srt s))).
Qed.

Lemma generation_prod_aux : forall e T Ts, e |- T : Ts ->
  forall U V, T = Prod U V -> exists s, Ts = Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  exists s2 ; auto.

  destruct (IHtyp1 U0 V0 H3).
  rewrite H4 in H1.
  induction (typ_sort H1).
  inversion H6.
  rewrite H8 in H2.
  rewrite H4 in H2.
  pose (coerce_propset_l H2).
  exists x ; auto.
Qed.

Lemma generation_prod : forall e U V Ts, e |- Prod U V : Ts ->
  exists s, Ts = Srt s.
Proof.
  intros.
  eapply generation_prod_aux with e (Prod U V) U V ; auto.
Qed.

Lemma generation_prod2_aux : forall e T Ts, e |- T : Ts ->
  forall U V, T = Prod U V -> forall s, Ts = Srt s ->
  (exists s', e |- U : Srt s') /\ (U :: e) |- V : Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  inversion H1.
  rewrite H4 in H.
  rewrite H5 in H0.
  rewrite H4 in H0.

  split.
  exists s1 ; auto.
  inversion H2.
  rewrite <- H6.
  assumption.

  rewrite H4 in H2.
  rewrite H4 in H0.
  induction (typ_sort H0).
  inversion H6.
  rewrite H8 in H2.
  pose (coerce_propset_r H2).

  apply (IHtyp1 U0 V0 H3 s0 e0).
Qed.

Lemma generation_prod2 : forall e U V s, e |- Prod U V : Srt s ->
  (exists s', e |- U : Srt s') /\ (U :: e) |- V : Srt s.
Proof.
  intros.
  eapply generation_prod2_aux  ; auto ; auto.
Qed.

Lemma generation_sum_aux : forall e T Ts, e |- T : Ts ->
  forall U V, T = Sum U V -> exists s, Ts = Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  exists s2 ; auto.
  inversion H1 ; intuition.
  inversion H3 ; inversion H6 ; auto.
  inversion H3 ; inversion H6 ; auto.

  destruct (IHtyp1 U0 V0 H3).
  rewrite H4 in H1.
  induction (typ_sort H1).
  inversion H6.
  rewrite H8 in H2.
  rewrite H4 in H2.
  pose (coerce_propset_l H2).
  exists x ; auto.
Qed.

Lemma generation_sum : forall e U V Ts, e |- Sum U V : Ts ->
  exists s, Ts = Srt s.
Proof.
  intros.
  eapply generation_sum_aux with e (Sum U V) U V ; auto.
Qed.

Lemma generation_sum2_aux : forall e T Ts, e |- T : Ts ->
  forall U V, T = Sum U V -> forall s, Ts = Srt s ->
  e |- U : Srt s /\ (U :: e) |- V : Srt s /\ sum_sort s s s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  inversion H2.
  rewrite <- H5.
  rewrite <- H6.
  inversion H3.
  rewrite H7 in H1.
  induction H1 ; intuition.
  rewrite H9.
  rewrite H4 in H.
  assumption.
  rewrite H9.
  rewrite H1 in H0.
  assumption.

  rewrite H9 ; unfold sum_sort ; intuition.
  rewrite H9.
  rewrite H4 in H.
  assumption.
  rewrite H9.
  rewrite H1 in H0.
  assumption.
  rewrite H9 ; unfold sum_sort ; intuition.

  destruct (IHtyp1 U0 V0 H3 s0).
  rewrite H4 in H2.
  apply (coerce_propset_r H2).
  intuition.
Qed.

Lemma generation_sum2 : forall e U V s, e |- Sum U V : Srt s ->
  e |- U : Srt s /\ (U :: e) |- V : Srt s /\ sum_sort s s s.
Proof.
  intros.
  eapply generation_sum2_aux with (Sum U V) (Srt s); auto.
Qed.

Lemma generation_subset_aux : forall e T Ts, e |- T : Ts ->
  forall U V, T = Subset U V -> Ts = Srt set.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  auto.

  pose (IHtyp1 U0 V0 H3).
  rewrite e0 in H2.
  exact (coerce_propset_l H2).
Qed.

Lemma generation_subset : forall e U V Ts, e |- Subset U V : Ts ->
  Ts = Srt set.
Proof.
  intros.
  eapply generation_subset_aux with e (Subset U V) U V ; auto.
Qed.

Lemma generation_subset2_aux : forall e T Ts, e |- T : Ts ->
  forall U V, T = Subset U V -> Ts = Srt set ->
  e |- U : Srt set /\ (U :: e) |- V : Srt prop.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  inversion H1.
  rewrite H4 in H.
  rewrite H5 in H0.
  rewrite H4 in H0.
  intuition.

  rewrite H4 in H2.
  pose (coerce_propset_r H2).
 
  apply (IHtyp1 U0 V0 H3 e0).
Qed.

Lemma generation_subset2 : forall e U V s, e |- Subset U V : Srt set ->
  (e |- U : Srt set) /\ (U :: e) |- V : Srt prop.
Proof.
  intros.
  eapply generation_subset2_aux  ; auto ; auto.
Qed.

Lemma var_sort_item : forall e t T, e |- t : T ->
  forall n, t = Ref n -> 
  forall s, T = (Srt s) -> item _ (Srt s) e n.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  inversion H1.

  rewrite H2 in H0.
  rewrite <- H4 ; auto.
  destruct H0.
  assert(x = Srt s).
  apply (inv_lift_sort) with (S n) ; auto.
  rewrite H5 in H3 ; assumption.

  rewrite H4 in H2.
  pose (coerce_propset_r H2).
  pose (IHtyp1 n H3 s0 e0).
  assumption.
Qed. 

(*
Lemma var_sort_dom_item : forall e n T, e |- Ref n : T ->
  forall s, type_dom T = (Srt s) -> 
  exists T', item_lift T' e n /\ type_dom T' = Srt s.
Admitted.

Lemma unique_var_dom_sort : forall e n T, e |- Ref n : T ->
  forall s, type_dom T = Srt s ->
  forall T', e |- Ref n : T' -> 
  forall s', type_dom T' = Srt s' -> s = s'.
Proof.
  intros.
  destruct (var_sort_dom_item H H0).
  destruct (var_sort_dom_item H1 H2).
  destruct H3 ; destruct H4.
  destruct H3 ; destruct H4.
  pose (fun_item _ _ _ _ _ H7 H8).
  rewrite <- e0 in H4.
  rewrite <- H4 in H3.
  rewrite <- H3 in H6.
  rewrite H6 in H5.
  inversion H5.
  auto.
Qed.
*)
Lemma unique_var_sort : forall e n s, e |- Ref n : Srt s ->
  forall s', e |- Ref n : Srt s' -> s = s'.
Proof.
  intros.
  pose (var_sort_item H (refl_equal (Ref n)) (refl_equal (Srt s))).
  pose (var_sort_item H0 (refl_equal (Ref n)) (refl_equal (Srt s'))).
  pose (fun_item _ _ _ _ _ i i0).
  inversion e0 ; auto.
Qed.

Lemma sort_of_app_aux : forall e t Ts, e |- t : Ts ->
  forall M N, t = App M N ->
  forall s, Ts = Srt s -> 
  (exists V, e |- M : Prod V (Srt s) /\ e |- N : V). 
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  inversion H1.

  induction (inv_subst_sort _ _ _ H2).
  rewrite H3 in H.
  destruct (typ_sort H).
  rewrite H7 in H0.
  pose (type_no_kind_prod_type H0).
  simpl in t.
  intuition.
  
  rewrite H3 in H0.
  rewrite H4 in H0.
  exists V ; intuition ; auto.
  rewrite <- H5 ; auto.

  rewrite H4 in H2.
  pose (coerce_propset_r H2).
  exact (IHtyp1 _ _ H3 _ e0).
Qed.

Lemma sort_of_app : forall e M N s, e |- App M N : Srt s ->
  exists V, e |- M : Prod V (Srt s) /\ e |- N : V.
Proof.
  intros. 
  eapply sort_of_app_aux ; auto ; auto ; auto.
Qed.


Lemma sort_of_app_aux2 : forall e t Ts, e |- t : Ts ->
  forall M N, t = App M N ->
  forall s, Ts = Srt s -> 
  forall s', ~ N = Srt s'.
Proof.
  intros.
  red ; intros.
  rewrite H1 in H.
  rewrite H0 in H.
  destruct (sort_of_app H).
  destruct H3.
  rewrite H2 in H4.
  pose (typ_sort H4).
  destruct a.
  rewrite H6 in H3.
  pose (type_no_kind_prod_type H3).
  simpl in t0.
  intuition.
Qed.

Lemma sort_of_app2 : forall e M N s, e |- App M N : Srt s -> forall s', ~ N = Srt s'.
Proof.
  intros. 
  eapply (sort_of_app_aux2 H) ; auto ; auto ; auto.
Qed.

Lemma strength_sort_judgement : forall T e s s', T :: e |- Srt s : Srt s' ->
  e |- Srt s : Srt s'.
Proof.
  intros.
  pose (typ_wf H).
  inversion w.
  pose (typ_wf H1).
  inversion H ; auto with coc.

  destruct (typ_sort H).
  inversion H11.
  rewrite H13 in H4.
  pose (type_has_no_kind H4).
  simpl in t0.
  intuition.
Qed.

Lemma type_sorted : forall e t T, e |- t : T ->
  T = Srt kind \/ exists s, e |- T : Srt s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc ; try discriminate ; 
 try (destruct H ; discriminate) ;  try (destruct H1 ; discriminate).

  right; exact (wf_sort_lift H H0).
 
  right.
  exists s2.
  apply type_prod with s1 ; auto.

  induction IHtyp2 ; try discriminate.
  induction H1.
  induction IHtyp1.
  rewrite H2 in H0.
  pose (type_no_kind_prod_type H0).
  simpl in t.
  intuition.

  induction H2.
  right.
  exists x.
  induction (generation_prod2 H1).
  replace (Srt x) with (subst v (Srt x)).
  apply (substitution H4 H).
  unfold subst ; unfold subst_rec ; auto.

  right.
  exists s3.
  apply type_sum with s1 s2 ; auto.

  induction IHtyp2.
  left ; assumption.
  induction H1.
  right.
  exists x ; auto.
  eapply strength_sort_judgement with T ; auto.
  
  induction IHtyp2.
  unfold sum_sort in H1.
  inversion H2.
  intuition ; try rewrite H4 in H5 ; try rewrite H4 in H1 ; try discriminate.
  right ; exists kind.
  pose (typ_wf H).
  induction H1 ; intuition ; try discriminate ; rewrite H5 ; auto with coc.
  
  induction IHtyp ; try discriminate.
  induction H0.
  induction (generation_sum2 H0).
  right ; exists x ; auto.

  induction IHtyp ; try discriminate.
  induction H0.
  induction (generation_sum2 H0).
  right.
  assert (e |- Pi1 t : U).
  apply type_pi1 with V ; auto.
  exists x.
  replace (Srt x) with (subst (Pi1 t) (Srt x)).
  destruct H2.
  apply (substitution H2 H3).
  unfold subst ; unfold subst_rec ; auto.
  
  right ; exists s ; auto.
Qed.
