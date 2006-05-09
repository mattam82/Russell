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

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Fixpoint type_range (t : term) : term :=
  match t with
  | Prod U V => type_range V
  | Sum U V => type_range V
  | _ => t
  end.

Definition type_dom (t : term) : term :=
  match t with
  | Prod U V => type_range U
  | Sum U V => type_range U
  | Subset U V => type_range U
  | _ => type_range t
  end.

Definition is_low_sort (s : term) := s = Srt set \/ s = Srt prop.

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

Lemma kind_is_prod_aux : forall G t T, G |- t : T -> T = Srt kind ->
  is_low_sort (type_range t).
Proof.
  induction 1 ; intros ; try discriminate ; simpl ; auto.
  unfold is_low_sort ; intuition.
  unfold is_low_sort ; intuition.
  induction (wf_sort_lift H H0).
  rewrite H1 in H2.
  elim (typ_not_kind H2) ; auto.
  
  pose (subst_to_sort _ H1 (typ_not_kind H)).

  pose (type_no_kind_type H0 (or_introl _ (refl_equal (Prod V Ur)))).
  simpl in t.
  destruct t.
  rewrite e0 in H3.
  simpl in H3.
  contradiction.

  pose (type_no_kind_type H (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0.
  destruct t0.
  rewrite H0 in H1.
  simpl in H1.
  contradiction.

  pose (type_no_kind_type H (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0.
  destruct t0.
  assert(Pi1 t <> Srt kind) ; try (unfold not ; intros ; discriminate).
  pose (subst_to_sort _ H0 H3).
  rewrite e0 in H2.
  simpl in H2.
  contradiction.

(*  pose (type_has_no_kind H).
  pose (type_has_no_kind H2).
  unfold subst in H3.
  pose (type_range_subst_not_kind _ _ 0 t0 t1).
  pose (type_no_kind_not_kind t2).
  contradiction.*)

  rewrite H3 in H0.
  pose (typ_not_kind H0).
  elim n ; auto.
Qed.

Lemma type_kind_range : forall G t, G |- t : Srt kind -> is_low_sort (type_range t).
Proof.
  intros.
  apply kind_is_prod_aux with G (Srt kind) ; auto.
Qed.

Lemma red_sort_eq : forall s t, red (Srt s) t -> t = Srt s.
Proof.
  simple induction 1; intros; auto with coc core arith sets.
  rewrite H1 in H2.
  inversion H2.
Qed.

Lemma sort_conv_eq : forall G T s, G |- T : Srt kind -> conv T (Srt s) -> T = Srt s.
Proof.
  intros.
  destruct (church_rosser _ _ H0).
  pose (red_sort_eq H2).
  rewrite e in H1.

  pose (type_kind_range H).
  unfold is_low_sort in i.
  induction T ; try (simpl in i ; destruct i ; inversion H1 ; try discriminate) ; auto with coc core.

  rewrite (conv_sort _ _ H0).
  auto.

  rewrite (conv_sort _ _ H0).
  auto.

  pose (conv_sort_prod s T1 T2).
  pose (sym_conv _ _ H0).
  contradiction.

  pose (conv_sort_prod s T1 T2).
  pose (sym_conv _ _ H0).
  contradiction.

  pose (conv_sort_sum s T1 T2).
  pose (sym_conv _ _ H0).
  contradiction.

  pose (conv_sort_sum s T1 T2).
  pose (sym_conv _ _ H0).
  contradiction.
Qed.

Lemma coerce_sort_l_in_kind : forall G A s s', G |- Srt s >> A : s' -> s' = kind.
Proof.
  intros.
  pose (coerce_sort_l H).
  pose (typ_sort t).
  intuition.
  inversion H1 ; auto.
Qed.

Lemma coerce_sort_r_in_kind : forall G A s s', G |- A >> Srt s : s' -> s' = kind.
Proof.
  intros.
  pose (coerce_sort_r H).
  pose (typ_sort t).
  intuition.
  inversion H1 ; auto.
Qed.

Lemma coerce_not_kind_l : forall G T s, ~ G |- Srt kind >> T : s.
Proof.
  red ; intros.
  pose (coerce_sort_l H).
  elim (typ_not_kind t).
  auto.
Qed.

Lemma coerce_not_kind_r : forall G T s, ~ G |- T >> Srt kind : s.
Proof.
  red ; intros.
  pose (coerce_sort_r H).
  elim (typ_not_kind t).
  auto.
Qed.

Lemma coerce_propset_l_aux : forall G Ts A s', G |- Ts >> A : s' ->
  forall s, Ts = Srt s ->  s' = kind -> A = Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto.

  rewrite H6 in H3.
  rewrite H7 in H0.
  rewrite H7 in H2.
  rewrite H7 in H1.
  pose (sym_conv _ _  H3).
  pose (sort_conv_eq H0 c).
  rewrite e0 in IHcoerce.
  pose (IHcoerce s0 (refl_equal (Srt s0)) H7).
  rewrite e1 in H5.
  pose (sym_conv _ _ H5).
  exact (sort_conv_eq H2 c0).
Qed.

Lemma coerce_propset_r_aux : forall G Ts A s', G |- A >> Ts : s' ->
  forall s, Ts = Srt s ->  s' = kind -> A = Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto.

  rewrite H6 in H5.
  rewrite H7 in H.
  rewrite H7 in H0.
  rewrite H7 in H1.
  pose (sort_conv_eq H1 H5).
  rewrite e0 in IHcoerce.
  pose (IHcoerce s0 (refl_equal (Srt s0)) H7).
  rewrite e1 in H3.
  exact (sort_conv_eq H H3).
Qed.

Lemma coerce_propset_l :  forall G s A s', G |- Srt s >> A : s' ->
  A = Srt s.
Proof.
  intros.
  apply coerce_propset_l_aux with G (Srt s) s'; auto.
  apply coerce_sort_l_in_kind with G A s ; auto.
Qed.

Lemma coerce_propset_r :  forall G s A s', G |- A >> Srt s : s' ->
  A = Srt s.
Proof.
  intros.
  apply coerce_propset_r_aux with G (Srt s) s'; auto.
  apply coerce_sort_r_in_kind with G A s ; auto.
Qed.

