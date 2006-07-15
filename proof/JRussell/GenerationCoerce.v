Require Import Lambda.Tactics.

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
Require Import Lambda.JRussell.Validity.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Fixpoint type_range (t : term) : term :=
  match t with
  | Prod U V => type_range V
  | _ => t
  end.

Lemma subst_to_sort : forall t t' s, subst t t' = Srt s -> t <> Srt s ->
  t' = Srt s.
Proof.
  induction t' ; intros ; try discriminate.
  unfold subst, subst_rec in H.
  assumption.

  unfold subst, subst_rec in H.
  generalize H.
  elim (lt_eq_lt_dec 0 n).
  intros a.
  induction a.
  intros ; discriminate.
  intros.
  rewrite lift0 in H1.
  contradiction.

  intros ; discriminate.
Qed.

Fixpoint is_low t : Prop :=
  match t with 
  | Prod T U => is_low U
  | Srt s => is_prop s
  | _ => False
  end.

Lemma red_sort_eq : forall s t, red (Srt s) t -> t = Srt s.
Proof.
  simple induction 1; intros; auto with coc core arith sets.
  rewrite H1 in H2.
  inversion H2.
Qed.

Lemma is_low_lift : forall t, is_low t -> forall n k, is_low (lift_rec n t k).
Proof.
  induction t ; simpl ; intros ; auto with coc.
  elim H.
Qed.

Lemma kind_is_prod_aux : forall G t T, G |-= t : T -> 
  T = Srt kind -> is_low t.
Proof.
  unfold is_prop ; induction 1 ; intros ; try discriminate ; simpl ; auto.

  unfold is_prop ; intuition.
  unfold is_prop ; intuition.
  
  pose (lift_eq_sort _ _ H0).
  rewrite e0 in H.
  elim (type_has_no_kind H).

  unfold lift ; apply is_low_lift.
  pose (lift_eq_sort _ _ H1).
  apply (IHtyp1 e0).

  pose (subst_to_sort _ H1 (typ_not_kind H)).
  
  pose (type_no_kind_type H0 (or_introl _ (refl_equal (Prod V Ur)))).
  simpl in t.
  destruct t.
  rewrite e0 in H3.
  simpl in H3.
  contradiction.
  
  inversion H2.
  rewrite H4 in H1.
  induction H1 ; intuition ; try discriminate.

  pose (type_no_kind_type H (or_intror _ (refl_equal (Sum U V)))).
  rewrite H0 in t0.
  simpl in t0.
  destruct t0.
  contradiction.

  assert(Pi1 t <> Srt kind).
  red ; intros ; discriminate.
  pose (subst_to_sort _ H0 H1).
  pose (type_no_kind_type H (or_intror _ (refl_equal (Sum U V)))).
  rewrite e0 in t0.
  simpl in t0.
  destruct t0.
  contradiction.
  
  rewrite H1 in H0.
  destruct (validity_coerce H0).
  elim (typ_not_kind H3).
  auto.
Qed.

Lemma type_kind_range : forall G t, G |-= t : Srt kind -> is_low t.
Proof.
  intros.
  apply kind_is_prod_aux with G (Srt kind) ; auto.
Qed.

Lemma sort_conv_eq : forall G T s, G |-= T : Srt kind -> conv T (Srt s) -> T = Srt s.
Proof.
  intros.
  destruct (church_rosser _ _ H0).
  pose (red_sort_eq H2).
  rewrite e in H1.

  pose (type_kind_range H).
  unfold is_low in i.
  induction T ; try (simpl in i ; destruct i ; inversion H1 ; try discriminate) ; auto with coc core.

  rewrite (conv_sort _ _ H0).
  auto.

  rewrite (conv_sort _ _ H0).
  auto.

  pose (conv_sort_prod s T1 T2).
  pose (sym_conv _ _ H0).
  contradiction.
Qed.

Lemma typ_sort : forall G s T, G |-= (Srt s) : T -> is_prop s /\ T = (Srt kind).
Proof.
  intros G s T H.
  induction_with_subterm (Srt s) H ; intuition ; try discriminate.

  injection y ; intro ; rewrite <- H ; unfold is_prop ; intuition.

  injection y ; intro ; rewrite <- H ; unfold is_prop ; intuition.

  pose (lift_eq_sort _ _ y).
  induction (IHtyp1 e0).
  auto.

  pose (lift_eq_sort _ _ y).
  induction (IHtyp1 e0).
  subst T ; auto.

  rewrite H3 in H0.
  pose (coerce_sort_l H0).
  elim (typ_not_kind t) ; auto.
Qed.

Lemma coerce_sort_l_in_kind : forall G A s s', G |-= Srt s >> A : s' -> s' = kind.
Proof.
  intros.
  pose (coerce_sort_l H).
  pose (typ_sort t).
  intuition.
  inversion H1 ; auto.
Qed.

Lemma coerce_sort_r_in_kind : forall G A s s', G |-= A >> Srt s : s' -> s' = kind.
Proof.
  intros.
  pose (coerce_sort_r H).
  pose (typ_sort t).
  intuition.
  inversion H1 ; auto.
Qed.

Lemma coerce_not_kind_l : forall G T s, ~ G |-= Srt kind >> T : s.
Proof.
  red ; intros.
  pose (coerce_sort_l H).
  elim (typ_not_kind t).
  auto.
Qed.

Lemma coerce_not_kind_r : forall G T s, ~ G |-= T >> Srt kind : s.
Proof.
  red ; intros.
  pose (coerce_sort_r H).
  elim (typ_not_kind t).
  auto.
Qed.

Lemma eq_conv : forall e t u T, e |-= t = u : T -> conv t u.
Proof.
  induction 1 ; simpl ; intros; auto with coc.

  unfold lift ; apply (conv_conv_lift) ; auto.

  apply (conv_conv_abs) ; auto.
  apply (conv_conv_app) ; auto.
  apply (conv_conv_sum) ; auto.
  apply (conv_conv_pair) ; auto.
  apply (conv_conv_sum) ; auto.
  apply (conv_conv_subset) ; auto.
  apply trans_conv_conv with N; auto.
Qed.

Lemma sort_eq_eq : forall G T s, G |-= T = (Srt s) : Srt kind -> T = Srt s.
Proof.
  intros.
  pose (eq_conv H).
  apply sort_conv_eq with G ; auto.
  apply (jeq_type_l H).
Qed.

Lemma coerce_propset_aux : forall G A B s', G |-= A >> B : s' ->
  (forall s, A = Srt s ->  s' = kind -> B = Srt s) /\
  (forall s, B = Srt s ->  s' = kind -> A = Srt s).
Proof.
  induction 1 ; simpl ; split ; intros ; try discriminate ; auto.

  subst.
  pose (jeq_sym H).
  apply (sort_eq_eq j).

  subst.
  apply (sort_eq_eq H).

  destruct IHcoerce.
  pose (lift_eq_sort _ _ H1).
  pose (H3 s0 e0 H2).
  rewrite e1 ; auto.

  destruct IHcoerce.
  pose (lift_eq_sort _ _ H1).
  pose (H4 s0 e0 H2).
  rewrite e1 ; auto.

  destruct IHcoerce.
  apply (H3 s0 H0 H1).

  destruct IHcoerce.
  apply (H2 s0 H0 H1).

  destruct IHcoerce1.
  destruct IHcoerce2.
  pose (H3 s0 H1 H2).
  apply (H5 s0 e0 H2).

  destruct IHcoerce1.
  destruct IHcoerce2.
  pose (H6 s0 H1 H2).
  apply (H4 s0 e0 H2).
Qed.

Lemma coerce_propset_l :  forall G s A s', G |-= Srt s >> A : s' ->
  A = Srt s.
Proof.
  intros.
  destruct (coerce_propset_aux H) ; auto.
  apply H0 ; auto with coc.
  apply coerce_sort_l_in_kind with G A s ; auto.
Qed.

Lemma coerce_propset_r :  forall G s A s', G |-= A >> Srt s : s' ->
  A = Srt s.
Proof.
  intros.
  destruct (coerce_propset_aux H) ; auto.
  apply H1 ; auto with coc.
  apply coerce_sort_r_in_kind with G A s ; auto.
Qed.

Fixpoint no_sort t : Prop :=
  match t with 
  | Prod T U => no_sort U
  | Srt s => False
  | _ => True
  end.

Lemma no_sort_lift : forall t, no_sort t -> forall n k, no_sort (lift_rec n t k).
Proof.
  induction t ; simpl ; intros ; auto.
  elim (le_gt_dec k n) ; auto.
Qed.

Fixpoint is_low_full t : Prop :=
  match t with 
  | Prod T U => is_low_full U
  | Srt s => is_prop s
  | _ => False
  end.

Lemma is_low_full_lift : forall t, is_low_full t -> forall n k, is_low_full (lift_rec n t k).
Proof.
  induction t ; simpl ; intros ; auto.
  elim (le_gt_dec k n) ; auto.
Qed.

Lemma sort_of_kinded_aux : forall G t T, G |-= t : T -> 
  forall s, T = Srt s -> 
  (s = kind -> is_low_full t) /\ (is_prop s -> no_sort t).
Proof.
  unfold is_prop ; induction 1 ; intros ; try discriminate ; simpl ; auto.

  unfold is_prop ; intuition.
  rewrite H1 in H ; discriminate.
  rewrite H1 in H ; discriminate.
  
  split ; intros ; unfold is_prop ; auto.
  intuition ; rewrite H1 in H ; discriminate.

  split ; intros.
  rewrite H1 in H0.
  pose (lift_eq_sort _ _ H0).
  rewrite e0 in H.
  elim (typ_not_kind H) ; auto.
  auto.

  split ; intros ; auto.
  rewrite H2 in H1.
  pose (lift_eq_sort _ _ H1).
  destruct (IHtyp1 _ e0).
  unfold lift ; apply is_low_full_lift ; auto.
  unfold lift ; apply no_sort_lift ; auto.
  pose (lift_eq_sort _ _ H1).
  destruct (IHtyp1 _ e0).
  apply H4 ; auto.
  
  split ; intros.
  rewrite H2 in H1.
  pose (subst_to_sort _ H1  (typ_not_kind H)).

  pose (type_no_kind_type H0 (or_introl _ (refl_equal (Prod V Ur)))).
  simpl in t.
  destruct t.
  rewrite e0 in H4.
  simpl in H4.
  contradiction.
  auto.
  
  inversion H2.
  rewrite H4 in H1.
  split ; intros.
  rewrite H3 in H1.
  induction H1 ; intuition ; try discriminate.

  auto.
  inversion H1.
  intuition ; intros ; try discriminate.

  split ; intros.
  rewrite H1 in H0.
  
  pose (type_no_kind_type H (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0.
  destruct t0.
  rewrite H0 in H2.
  simpl in H2.
  contradiction.
  
  auto.

  split ; intros ; auto.
  pose (type_no_kind_type H (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0.
  destruct t0.
  assert(Pi1 t <> Srt s).
  red ; intros ; discriminate.
  pose (subst_to_sort _ H0 H4).
  rewrite H1 in e0.
  rewrite e0 in H3.
  simpl in H3.
  contradiction.

  assert(s = kind).
  pose (coerce_sort_r H0).
  rewrite H1 in t0.
  destruct (typ_sort t0).
  inversion H3.
  auto.

  split ; intros.
  rewrite H3 in H1.
  rewrite H1 in H0.
  pose (coerce_sort_r H0).
  elim (typ_not_kind t0) ; auto.
  rewrite H1 in H0.
  pose (coerce_propset_r H0).
  destruct (IHtyp s0 e0).
  auto.
Qed.

Lemma sorts_of_sorted : forall G t s, G |-= t : Srt s -> 
  (s = kind -> is_low_full t) /\ (is_prop s -> no_sort t).
Proof.
  intros.
  apply sort_of_kinded_aux with G (Srt s) ; auto ; auto.
Qed. 

Lemma sort_of_kinded : forall G t, G |-= t : Srt kind -> 
  is_low_full t.
Proof.
  intros ; destruct (sorts_of_sorted H).
  apply H0 ; auto.
Qed.

Lemma sort_of_propset : forall G t s, G |-= t : Srt s -> 
  is_prop s -> no_sort t.
Proof.
  intros ; destruct (sorts_of_sorted H).
  apply H2 ; auto.
Qed.


