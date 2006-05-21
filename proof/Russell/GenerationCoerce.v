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

Lemma kind_is_prod_aux : forall G t T, G |- t : T -> 
  T = Srt kind -> is_low t.
Proof.
  unfold is_prop ; induction 1 ; intros ; try discriminate ; simpl ; auto.

  unfold is_prop ; intuition.
  unfold is_prop ; intuition.
  
  induction (wf_sort_lift H H0).
  elim (typ_not_kind H2) ; auto.

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
  
  rewrite H3 in H2.
  pose (coerce_sort_r H2).
  elim (typ_not_kind t0).
  auto.
Qed.

Lemma type_kind_range : forall G t, G |- t : Srt kind -> is_low t.
Proof.
  intros.
  apply kind_is_prod_aux with G (Srt kind) ; auto.
Qed.


Lemma sort_conv_eq : forall G T s, G |- T : Srt kind -> conv T (Srt s) -> T = Srt s.
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

Fixpoint no_sort t : Prop :=
  match t with 
  | Prod T U => no_sort U
  | Srt s => False
  | _ => True
  end.

Fixpoint is_low_full t : Prop :=
  match t with 
  | Prod T U => is_low_full U
  | Srt s => is_prop s
  | _ => False
  end.

Lemma sort_of_kinded_aux : forall G t T, G |- t : T -> 
  forall s, T = Srt s -> 
  (s = kind -> is_low_full t) /\ (is_prop s -> no_sort t).
Proof.
  unfold is_prop ; induction 1 ; intros ; try discriminate ; simpl ; auto.

  unfold is_prop ; intuition.
  rewrite H2 in H0 ; discriminate.
  rewrite H2 in H0 ; discriminate.
  
  split ; intros ; unfold is_prop ; auto.
  intuition ; rewrite H2 in H0 ; discriminate.

  split ; intros.
  rewrite H2 in H1.
  induction (wf_sort_lift H H0).
  rewrite H1 in H3.
  elim (typ_not_kind H3) ; auto.
  auto.

  split ; intros ; auto.
  rewrite H2 in H1.
  pose (subst_to_sort _ H1 (typ_not_kind H)).

  pose (type_no_kind_type H0 (or_introl _ (refl_equal (Prod V Ur)))).
  simpl in t.
  destruct t.
  rewrite e0 in H4.
  simpl in H4.
  contradiction.
  
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
  pose (coerce_sort_r H2).
  rewrite H3 in t0.
  destruct (typ_sort t0).
  inversion H5.
  auto.

  destruct (IHtyp3 kind) ; rewrite <- H4 ; auto.
  destruct (IHtyp2 kind) ; try rewrite <- H4 ; auto.
  split ; intros.
  rewrite H4 in H9.
  rewrite H9 in H3.
  rewrite H3 in H7.
  unfold is_low, is_prop in H7 ; simpl in H7.
  destruct (H7 (refl_equal kind)) ; discriminate.

  clear H6 H5 H7 H8.
  rewrite H3 in H2.
  pose (coerce_propset_r H2).
  destruct (IHtyp1 s0 e0).
  auto.
Qed.

Lemma sorts_of_sorted : forall G t s, G |- t : Srt s -> 
  (s = kind -> is_low_full t) /\ (is_prop s -> no_sort t).
Proof.
  intros.
  apply sort_of_kinded_aux with G (Srt s) ; auto ; auto.
Qed. 

Lemma sort_of_kinded : forall G t, G |- t : Srt kind -> 
  is_low_full t.
Proof.
  intros ; destruct (sorts_of_sorted H).
  apply H0 ; auto.
Qed.

Lemma sort_of_propset : forall G t s, G |- t : Srt s -> 
  is_prop s -> no_sort t.
Proof.
  intros ; destruct (sorts_of_sorted H).
  apply H2 ; auto.
Qed.


