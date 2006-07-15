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
Require Import Lambda.JRussell.Validity.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Lemma lift_rec_eq_sort : forall t n k s, lift_rec n t k = Srt s -> t = Srt s.
Proof.
induction t ; simpl ; intros ; auto with coc core ; try discriminate.

generalize H ; clear H ; elim (le_gt_dec k n) ; intros ; discriminate.
Qed.

Lemma lift_eq_sort : forall t n s, lift n t = Srt s -> t = Srt s.
Proof.
unfold lift ; intros ; apply lift_rec_eq_sort with n 0 ; auto.
Qed.

Lemma typ_not_kind : forall G t T, G |-= t : T -> t <> Srt kind.
Proof.
induction 1 ; simpl ; red ; intros ; try discriminate.
pose (lift_eq_sort _ _ H1).
contradiction.
contradiction.
Qed.

Lemma typ_not_kind2 : forall G T, ~ G |-= Srt kind : T.
Proof.
  unfold not ; intros.
  apply (typ_not_kind H).
  auto.
Qed.

Hint Resolve lift_eq_sort typ_not_kind2 : coc.

Fixpoint type_no_kind (t : term) : Prop :=
  match t with
  | Prod U V => type_no_kind U /\ type_no_kind V
  | Sum U V => type_no_kind U /\ type_no_kind V
  | Srt kind => False
  | _ => True
  end.

Lemma type_no_kind_lift : forall t, type_no_kind t -> forall n k, type_no_kind (lift_rec n t k).
Proof.
  induction t ; simpl ; intros ; auto with coc.
  elim (le_gt_dec k n) ; auto.
  intuition ; auto with coc.
  intuition ; auto with coc.
Qed.

Lemma type_has_no_kind : forall G t T, G |-= t : T -> type_no_kind t.
Proof.
  induction 1; simpl ; intros ; auto with coc ; try discriminate.
  unfold lift ; apply type_no_kind_lift ; auto.
Qed.

Lemma type_no_kind_not_kind : forall t, type_no_kind t -> t <> Srt kind.
Proof.
  induction t ; unfold not ; intros ; try discriminate.
  simpl in H.
  inversion H0.
  rewrite H2 in H.
  auto.
Qed.

Lemma lift_type_range_eq_sort : forall n t k, type_no_kind (lift_rec n t k) -> 
  type_no_kind t.
Proof.
  induction t ; simpl ; intros ; try discriminate ; auto.

  intuition.
  apply IHt1 with k ; auto.
  apply IHt2 with (S k) ; auto.

  intuition.
  apply IHt1 with k ; auto.
  apply IHt2 with (S k) ; auto.
Qed.

Lemma type_range_subst_not_kind : forall u v n, type_no_kind u ->
  type_no_kind v -> type_no_kind (subst_rec u v n).
Proof.
  induction v ; simpl ; intros ; try discriminate ; auto.

  elim (lt_eq_lt_dec n0 n) ; intros.
  induction a ; simpl ; intros ; unfold not ; intros ; try discriminate ; auto.
  unfold lift ; apply (type_no_kind_lift); auto.
  auto.

  intuition.
  intuition.
Qed.
 
Lemma type_no_kind_type : forall G t T, G |-= t : T -> 
  forall U V, (T = Prod U V \/ T = Sum U V) -> type_no_kind T.
Proof.
  induction 1 using typ_dep with
  (P := fun G t T => fun H : G |-= t : T =>
  forall U V, (T = Prod U V \/ T = Sum U V) -> type_no_kind T)
 ; simpl ; intros ; auto with coc ; try discriminate ; 
 try (destruct H ; discriminate) ;  try (destruct H1 ; discriminate).

  unfold lift ; apply type_no_kind_lift.
  apply (type_has_no_kind H).

  unfold lift ; apply type_no_kind_lift.
  destruct H1.
  destruct T ; simpl in H1 ; try discriminate.
  apply IHtyp1 with T1 T2 ; auto with coc.
  destruct T ; simpl in H1 ; try discriminate.
  apply IHtyp1 with T1 T2 ; auto with coc.
  
  destruct H2 ; try discriminate.
  inversion H2 ; subst.
  intuition ; eapply type_has_no_kind ; eauto with coc.

  unfold subst ; apply type_range_subst_not_kind ; auto.
  apply (type_has_no_kind H).
  destruct (IHtyp2 V Ur).
  left ; auto.
  auto.

  destruct H3 ; try discriminate.
  inversion H3 ; subst.
  intuition ; eapply type_has_no_kind ; eauto with coc.

  destruct (IHtyp U V).
  right ; auto.
  auto.

  unfold subst ; apply type_range_subst_not_kind ; auto.
  simpl ; auto.
  destruct (IHtyp U V).
  right ; auto.
  auto.
  
  destruct (validity_coerce c).
  apply (type_has_no_kind H2).
Qed.

Lemma type_no_kind_prod_type : forall G t U V, 
  G |-= t : Prod U V -> type_no_kind (Prod U V).
Proof.
  intros.
  pose (type_no_kind_type H (or_introl _ (refl_equal (Prod U V)))).
  simpl in t0.
  intuition.
  simpl ; auto.
Qed.

Lemma type_no_kind_sum_type : forall G t U V, 
  G |-= t : Sum U V -> type_no_kind (Sum U V).
Proof.
  intros.
  pose (type_no_kind_type H (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0.
  intuition.
  simpl.
  intuition.
Qed.
 