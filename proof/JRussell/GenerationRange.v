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
Require Import Lambda.JRussell.Thinning.
Require Import Lambda.JRussell.Substitution.
Require Import Lambda.JRussell.Coercion.
Require Import Lambda.JRussell.Generation.
Require Import Lambda.JRussell.Validity.
Require Import Lambda.JRussell.GenerationNotKind.
Require Import Lambda.JRussell.GenerationCoerce.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.


Lemma type_range_lift : forall n t k s, type_range (lift_rec n t k) = Srt s -> 
  type_range t = Srt s.
Proof.
  induction t ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  generalize H ; clear H.
  elim (le_gt_dec k n0) ;  simpl ; intros ; try discriminate.
  apply IHt2 with (S k) ; auto.
Qed.

Lemma type_range_lift_inv : forall n t k s, type_range t = Srt s ->
  type_range (lift_rec n t k) = Srt s.
Proof.
  induction t ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
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

  unfold lift in H1 ; pose (type_range_lift _ _  _ H1).
  rewrite (IHtyp1 _ e0) ; auto.
  
  apply IHtyp2 with s ; auto.
  
  rewrite (IHtyp _ H1) in H0.
  elim (typ_not_kind (coerce_sort_l H0)) ; auto.
Qed.

Lemma term_type_range_not_kind : forall e t T, e |-= t : T ->
  forall s, type_range t = Srt s -> s <> kind. 
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  
  inversion H.
  unfold not ; intros ; discriminate.
  inversion H.
  unfold not ; intros ; discriminate.
  unfold lift in H1 ; pose (type_range_lift _ _ _ H1).
  apply (IHtyp1 _ e0).
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

Lemma eq_dom : 
  forall e A B s, e |-= A = B : Srt s -> 
  forall s', 
  (type_range A = Srt s' -> type_range B = Srt s').
Proof.
  intros.
  pose (term_type_range_kinded (jeq_type_l H) H0).
  inversion e0.
  rewrite H2 in H.
  pose (sort_of_kinded (jeq_type_l H1)).
  pose (sort_of_kinded (jeq_type_r H1)).
  pose (eq_conv H).
  apply (@conv_dom _ _ c s' i i0 H0).
Qed.

Lemma type_range_sub : forall e T U s, e |-= T >> U : s ->
  forall s0, (type_range U = Srt s0 -> type_range T = Srt s0) /\
  (type_range T = Srt s0 -> type_range U = Srt s0).
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  
  split ; intros.
  apply (eq_dom (jeq_sym H) H0).
  apply (eq_dom H H0).

  destruct (IHcoerce s0).
  intuition.
  unfold lift in H3.
  pose (type_range_lift _ _ _ H3).
  pose (H1 e0).
  unfold lift.
  apply (type_range_lift_inv) ; auto.


  unfold lift in H3.
  pose (type_range_lift _ _ _ H3).
  pose (H2 e0).
  unfold lift.
  apply (type_range_lift_inv) ; auto.

  split ; intros ; discriminate.

  split ; intros ; try discriminate.
  pose (coerce_sort_r H).
  
  pose (term_type_range_kinded t H3).
  discriminate.

  split ; intros ; try discriminate.
  pose (term_type_range_kinded H0 H3).
  discriminate.

  destruct (IHcoerce s0).
  intuition.

  destruct (IHcoerce1 s0).
  destruct (IHcoerce2 s0).
  split ; intros ; auto.
Qed.

Lemma var_sort_range_item_aux : forall e t T, e |-= t : T ->
  forall n, t = Ref n -> 
  forall s, type_range T = (Srt s) -> 
  exists T', item_lift T' e n /\ type_range T' = Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  induction T ; simpl ; simpl in H1 ; try discriminate.
  exists (Srt s1).
  split.
  exists (Srt s1) ; simpl ; auto.
  inversion H0.
  auto with coc.
  simpl ; auto.

  inversion H0.
  subst.
  exists (lift 1 (Prod T1 T2)).
  split ; simpl ; auto.
  exists (Prod T1 T2) ; auto with coc.

  destruct t ; simpl in H1 ; try discriminate.
  unfold lift in H2.
  pose (type_range_lift _ _ _ H2).
  destruct n ; simpl.
  inversion H1.
  pose (IHtyp1 _ (refl_equal (Ref n0)) _ e0).
  destruct e1.
  exists (lift 1 x).
  intuition ; auto with coc.
  destruct H4.
  inversion H1.
  subst.
  exists x0.
  pattern (lift (S (S n)) x0).
  rewrite simpl_lift.
  auto.
  apply item_tl ; auto.
  unfold lift; apply type_range_lift_inv ; auto.

  destruct (type_range_sub H0 s0).
  exact (IHtyp n H1 s0 (H3 H2)).
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

  unfold lift in H1 ; pose (inv_lift_app _ _ H1).
  destruct_exists.
  subst.

  destruct(IHtyp1 _ _ (refl_equal (App x x0)) s0).
  unfold lift in H2 ; apply (type_range_lift _ _ _ H2).
  destruct_exists.
  exists (lift_rec 1 x1 0).
  exists (lift_rec 1 x2 1).
  split ; auto with coc.
  eapply type_weak_weak with e U s e ; eauto with coc.
  split.
  change (Prod (lift_rec 1 x1 0) (lift_rec 1 x2 1)) with
  (lift_rec 1 (Prod x1 x2) 0).
  eapply type_weak_weak with e U s e ; eauto with coc.

  intuition.
  left ; eapply type_range_lift_inv ; eauto.
  right ; eapply type_range_lift_inv ; eauto.
  
  inversion H1 ; subst.
  exists V ; exists Ur ; intuition.
  induction (type_range_subst _ _ _ H2) ; intuition.

  destruct (@type_range_sub _ _ _ _ H0 s0).
  pose (H3 H2).
  exact (IHtyp _ _ H1 _ e0).
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

  unfold lift in H1 ; pose (inv_lift_abs _ _ H1).
  destruct_exists.
  subst.

  destruct(IHtyp1 _ _ (refl_equal (Abs x x0)) s0).
  unfold lift in H2 ; apply (type_range_lift _ _ _ H2).
  destruct_exists.
  exists x1 ; exists x2 ; exists (lift_rec 1 x3 1).
  intuition ; auto with coc.
  change (Srt x1) with (lift_rec 1 (Srt x1) 0).
  eapply type_weak_weak with e U s e ; eauto with coc.
  eapply type_weak_weak with e U s (x :: e) ; eauto with coc.
  change (Srt x2) with (lift_rec 1 (Srt x2) 1).
  eapply type_weak_weak with e U s (x :: e) ; eauto with coc.

  eapply type_range_lift_inv ; eauto.
  
  inversion H2 ; subst.
  exists s1 ; exists s2 ; exists U ; intuition.

  destruct (@type_range_sub _ _ _ _ H0 s0).
  pose (H3 H2).
  exact (IHtyp _ _ H1 _ e0).
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
  unfold lift in H2 ; pose (type_range_lift _ _ _ H2).
  pose (inv_lift_pair _ _ H1) ; destruct_exists.
  subst.
  destruct (IHtyp1 _ _ _ (refl_equal (Pair a b c)) s0) ; auto.

  pose (IHtyp _ _ _ H1 s0).
  red ; intros.
  destruct (type_range_sub H0 s0).
  pose (H3 H2).
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

  pose (inv_lift_sum _ _ H1) ; destruct_exists.
  subst.
  destruct (IHtyp1 x x0) ; auto.
  split ; intros; auto with coc.
  red ; intros.
  pose (type_range_lift _ _ _ H4).
  pose (H2 s0) ; auto.
  red ; intros.
  pose (type_range_lift _ _ _ H4).
  pose (H3 s0) ; auto.

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

  pose (inv_lift_pi1 _ _ H1) ; destruct_exists.
  red ; intros.
  subst.
  unfold lift in H4 ; pose (type_range_lift _ _ _ H4).
  pose (IHtyp1 _ (refl_equal (Pi1 x)) s0).
  auto.
  
  red ; intros.
  inversion H0.
  subst.
  induction (validity_typ H) ; try discriminate.
  induction H2.
  induction (sort_of_sum H2).
  elim (H3 s) ; auto.
  
  red ; intros.
  destruct (type_range_sub H0 s0).
  pose (H3 H2).
  apply (IHtyp _ H1 s0 e0).
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

  pose (inv_lift_pi2 _ _ H1) ; destruct_exists.
  red ; intros.
  subst.
  unfold lift in H4 ; pose (type_range_lift _ _ _ H4).
  pose (IHtyp1 _ (refl_equal (Pi2 x)) s0).
  auto.
  
  red ; intros.
  inversion H0.
  subst.
  induction (validity_typ H) ; try discriminate.
  induction H2.
  induction (sort_of_sum H2).
  unfold subst in H1.
  destruct (type_range_subst _ _ _ H1).
  discriminate.

  elim (H4 s) ; auto.
  
  red ; intros.
  destruct (type_range_sub H0 s0).
  pose (H3 H2).
  apply (IHtyp _ H1 s0 e0).
Qed.

Lemma sort_of_pi2_range :  forall e t Ts, e |-= Pi2 t : Ts ->
  forall s, type_range Ts <> Srt s.
Proof.
  intros. 
  apply sort_of_pi2_range_aux with e (Pi2 t) t  ; auto ; auto.
Qed.

Lemma type_range_subst_inv : forall t u n s, type_range t = Srt s -> 
  type_range (subst_rec u t n) = Srt s.
Proof.
  induction t ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
Qed.

