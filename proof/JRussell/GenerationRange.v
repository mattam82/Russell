Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Conv_Dec.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.JRussell.Types.
Require Import Lambda.JRussell.Thinning.
Require Import Lambda.JRussell.Substitution.
Require Import Lambda.JRussell.Coercion.
Require Import Lambda.JRussell.GenerationNotKind.
Require Import Lambda.JRussell.GenerationCoerce.
Require Import Lambda.JRussell.Generation.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Lemma type_range_lift : forall n t k s, type_range (lift_rec n t k) = Srt s -> 
  type_range t = Srt s.
Proof.
  induction t ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  generalize H ; clear H.
  elim (le_gt_dec k n0) ;  simpl ; intros ; try discriminate.
  apply IHt2 with (S k) ; auto.
Qed.

Lemma type_range_subst : forall t u n s, type_range (subst_rec t u n) = Srt s ->
  type_range t = Srt s \/ type_range u = Srt s.
Proof.
  induction u ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  generalize H.
  elim (lt_eq_lt_dec n0 n) ; simpl ; try (intros ; discriminate).
  intro a ; case a ; clear a ; simpl ; intros ; try discriminate.
  unfold lift in H0.
  left ; exact (type_range_lift _ _ _ H0).
  
  apply IHu2 with (S n) ; auto.
Qed.

Lemma no_sort_type_range : forall A, no_sort A -> forall s, type_range A <> Srt s.
Proof.
  induction A ; simpl ; intros ; intuition ; try discriminate ; auto.
  apply H1 with s ; auto.
Qed.


Lemma term_type_range_kinded : forall e t T, e |-= t : T ->
  forall s, type_range t = Srt s -> T = Srt kind. 
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  
  apply IHtyp2 with s ; auto.
  
  rewrite (IHtyp1 _ H3) in H1.
  elim typ_not_kind2 with e (Srt s) ; auto.
Qed.

Lemma term_type_range_not_kind : forall e t T, e |-= t : T ->
  forall s, type_range t = Srt s -> s <> kind. 
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  
  inversion H0.
  unfold not ; intros ; discriminate.
  inversion H0.
  unfold not ; intros ; discriminate.
Qed.

Lemma conv_dom : 
  forall A B, conv A B -> 
  forall s', 
  is_low_full A -> is_low_full B ->
  (type_range A = Srt s' -> type_range B = Srt s').
Proof.
  induction A ; simpl ; intros ; try discriminate ; try contradiction.
  
  induction B ; simpl ; intros ; try discriminate ; try contradiction.
  pose (conv_sort _ _ H).
  rewrite <- e.
  auto.

  elim conv_sort_prod with s B1 B2 ; auto with coc.

  induction B ; simpl ; intros ; try discriminate ; try contradiction.

  elim conv_sort_prod with s A1 A2 ; auto with coc.

  pose (inv_conv_prod_r _ _ _ _ H).
  simpl in H1.
  apply (IHA2 _ c s' H0 H1).
  assumption.
Qed.

Lemma type_range_sub : forall e T U s, e |-= T >> U : s ->
  forall s0, (type_range U = Srt s0 -> type_range T = Srt s0).
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  pose (coerce_sort_r H).
  
  pose (term_type_range_kinded t H1).
  discriminate.

  pose (term_type_range_kinded H2 H6).
  inversion e0.
  rewrite H8 in H.
  rewrite H8 in H0.
  rewrite H8 in H1.
  rewrite H8 in H2.
  pose (sort_of_kinded H).
  pose (sort_of_kinded H0).
  pose (sort_of_kinded H1).
  pose (sort_of_kinded H7).
  pose (@conv_dom _ _ (sym_conv _ _ H5) s0 i2 i1).
  pose (e1 H6).
  pose (IHcoerce s0 e2).
  apply (@conv_dom _ _  (sym_conv _ _ H3) s0 i0 i) ; auto.
Qed.

Lemma var_sort_range_item_aux : forall e t T, e |-= t : T ->
  forall n, t = Ref n -> 
  forall s, type_range T = (Srt s) -> 
  exists T', item_lift T' e n /\ type_range T' = Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  inversion H1.
  
  induction T ; simpl ; simpl in H2 ; try discriminate.
  
  rewrite H2 in H0.
  rewrite <- H4 ; auto.
  destruct H0.
  assert(x = Srt s).
  apply (inv_lift_sort) with (S n) ; auto.
  inversion H2.
  exists (Srt s).
  simpl ; intuition ; auto.
  exists (Srt s) ; unfold lift ; simpl ; auto.
  rewrite H5 in H3 ; assumption.
  
  inversion H1.
  exists (Prod T1 T2).
  intuition ; auto.
  rewrite <- H5 ; assumption.
  
  exact (IHtyp1 n H3 s0 (type_range_sub H2 H4)).
Qed. 

Lemma var_sort_range_item : forall e n T, e |-= Ref n : T ->
  forall s, type_range T = (Srt s) -> 
  exists T', item_lift T' e n /\ type_range T' = Srt s.
Proof.
  intros.
  eapply var_sort_range_item_aux with (Ref n) T; auto ; auto.
Qed.

Lemma unique_var_range_sort : forall e n T, e |-= Ref n : T ->
  forall s, type_range T = Srt s ->
  forall T', e |-= Ref n : T' -> 
  forall s', type_range T' = Srt s' -> s = s'.
Proof.
  intros.
  destruct (var_sort_range_item H H0).
  destruct (var_sort_range_item H1 H2).
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


Lemma sort_of_app_range_aux : forall e t Ts, e |-= t : Ts ->
  forall M N, t = App M N ->
  forall s, type_range Ts = Srt s ->
  exists V, exists T,  e |-= N : V /\ e |-= M : Prod V T /\
  (type_range T = (Srt s) \/ type_range N = Srt s).
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  inversion H1.

  induction (type_range_subst _ _ _ H2).
  rewrite <- H5.
  exists V.
  exists Ur.
  rewrite <- H4.
  split ; auto.
  
  exists V ; auto.
  exists Ur.
  rewrite <- H5.
  rewrite <- H4.
  split ; auto.
  
  pose (type_range_sub H2 H4).
  exact (IHtyp1 _ _ H3 _ e0).
Qed.

Lemma sort_of_app_range : forall e M N Ts, e |-= App M N : Ts ->
  forall s, type_range Ts = Srt s ->
  exists V, exists T,  e |-= N : V /\ e |-= M : Prod V T /\
  (type_range T = (Srt s) \/ type_range N = Srt s).
Proof.
  intros. 
  apply sort_of_app_range_aux with (App M N) Ts  ; auto ; auto.
Qed.

Lemma sort_of_abs_range_aux : forall e t Ts, e |-= t : Ts ->
  forall M N, t = Abs M N ->
  forall s, type_range Ts = Srt s ->
  exists s1, exists s2, exists T, e |-= M : (Srt s1) /\ M :: e |-= N : T /\
  M :: e |-= T : Srt s2 /\ type_range T = (Srt s).
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  exists s1 ; exists s2.
  exists U.
  inversion H2.
  rewrite <- H5 ; rewrite <- H6.
  intuition.

  apply (IHtyp1) ; auto.
  
  apply (type_range_sub H2 H4).
Qed.

Lemma sort_of_abs_range : forall e M N Ts, e |-= Abs M N : Ts ->
  forall s, type_range Ts = Srt s ->
  exists s1, exists s2, exists T, e |-= M : (Srt s1) /\ M :: e |-= N : T /\
  M :: e |-= T : Srt s2 /\ type_range T = (Srt s).
Proof.
  intros. 
  apply sort_of_abs_range_aux with (Abs M N) Ts  ; auto ; auto.
Qed.

Lemma sort_of_pair_range_aux : forall e t Ts, e |-= t : Ts ->
  forall T u v, t = Pair T u v ->
  forall s, type_range Ts <> Srt s.
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  unfold not ; intros.
  pose (type_range_sub H2 H4).
  pose (IHtyp1 _ _ _ H3 s0).
  contradiction.
Qed.

Lemma sort_of_pair_range : forall e T u v Ts, e |-= Pair T u v : Ts ->
  forall s, type_range Ts <> Srt s.
Proof.
  intros. 
  apply (@sort_of_pair_range_aux e (Pair T u v) Ts H T u v) ; auto ; auto.
Qed.

Lemma sum_sort_prop : forall s s' s'', sum_sort s s' s'' -> 
  is_prop s /\ s = s' /\ s' = s''.
Proof.
  induction 1.
  destruct H.
  destruct H0.
  rewrite H ; rewrite H0 ; rewrite H1.
  unfold is_prop ; intuition.
  destruct H.
  destruct H0.
  rewrite H ; rewrite H0 ; rewrite H1.
  unfold is_prop ; intuition.
Qed.

Lemma sort_of_sum_aux : forall e T Ts, e |-= T : Ts -> 
  forall U V, T = Sum U V -> 
  (forall s, type_range U <> Srt s) /\ 
  (forall s, type_range V <> Srt s).
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  
  pose (sum_sort_prop H1).
  destruct a.
  destruct H4.
  rewrite <- H4 in H0.
  pose (sort_of_propset H H3).
  pose (sort_of_propset H0 H3).
  pose (no_sort_type_range _ n).
  pose (no_sort_type_range _ n0).
  inversion H2.
  rewrite <- H7.
  rewrite <- H8.
  intuition.
Qed.

Lemma sort_of_sum : forall e U V T, e |-= Sum U V : T -> 
  (forall s, type_range U <> Srt s) /\ 
  (forall s, type_range V <> Srt s).
Proof.
  intros ; apply sort_of_sum_aux with e (Sum U V) T ; auto ; auto.
Qed.

Lemma sort_of_pi1_range_aux : forall e t Ts, e |-= t : Ts ->
  forall u, t = Pi1 u ->
  forall s, type_range Ts <> Srt s.
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  induction (type_sorted H) ; try discriminate.
  induction H1.
  induction (sort_of_sum H1).
  apply H2 ; auto.
  
  red ; intros.
  pose (type_range_sub H2 H4).
  apply (IHtyp1 _ H3 s0 e0).
Qed.

Lemma sort_of_pi1_range :  forall e t Ts, e |-= Pi1 t : Ts ->
  forall s, type_range Ts <> Srt s.
Proof.
  intros. 
  apply (@sort_of_pi1_range_aux _ _ _  H t) ; auto ; auto.
Qed.

Lemma sort_of_pi2_range_aux : forall e t Ts, e |-= t : Ts ->
  forall u, t = Pi2 u ->
  forall s, type_range Ts <> Srt s.
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  induction (type_sorted H) ; try discriminate.
  induction H1.
  induction (sort_of_sum H1).
  red ; intros.
  
  induction (type_range_subst _ _ _ H4).
  simpl in H5 ; discriminate.
  pose (H3 s);contradiction.

  red ; intros.
  pose (type_range_sub H2 H4).
  apply (IHtyp1 u H3 s0 e0) ; auto.
Qed.

Lemma sort_of_pi2_range :  forall e t Ts, e |-= Pi2 t : Ts ->
  forall s, type_range Ts <> Srt s.
Proof.
  intros. 
  apply sort_of_pi2_range_aux with e (Pi2 t) t  ; auto ; auto.
Qed.

Lemma type_range_subst2 : forall t u n s, type_range t = Srt s -> 
  type_range (subst_rec u t n) = Srt s.
Proof.
  induction t ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
Qed.

