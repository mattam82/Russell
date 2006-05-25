Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Conv_Dec.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import JRussell.Types.
Require Import JRussell.Thinning.
Require Import JRussell.Substitution.
Require Import JRussell.Coercion.

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
red ; intros.
rewrite H0 in H.
pose (typ_sort H).
induction a.
unfold is_prop in H1.
induction H1 ; discriminate.
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

Lemma type_has_no_kind : forall G t T, G |-= t : T -> type_no_kind t.
Proof.
  induction 1; simpl ; intros ; auto with coc ; try discriminate.
Qed.

Lemma type_no_kind_not_kind : forall t, type_no_kind t -> t <> Srt kind.
Proof.
  induction t ; unfold not ; intros ; try discriminate.
  simpl in H.
  inversion H0.
  rewrite H2 in H.
  auto.
Qed.
(*
Lemma type_range_not_kind_ps : forall G t T, G |-= t : T -> 
  forall U V, t = Prod U V \/ t = Sum U V -> type_range U <> Srt kind /\
  type_range V <> Srt kind.
Proof.
  induction 1; simpl ; intros ; auto with coc ; try (intuition ; discriminate).
  destruct H1.

  inversion H1.
  rewrite <- H3.
  rewrite <- H4.
  split.
  apply (type_range_not_kind H).
  apply (type_range_not_kind H0).
  discriminate.

  inversion H1.
  discriminate.
  inversion H2.
  rewrite <- H4.
  rewrite <- H5.
  split.
  apply (type_range_not_kind H).
  apply (type_range_not_kind H0).
Qed.
*)
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

Lemma type_no_kind_lift : forall n t k, type_no_kind t ->
  type_no_kind (lift_rec n t k).
Proof.
  induction t ; simpl ; intros ; try discriminate ; auto.

  elim (le_gt_dec k n0) ; simpl ; intros ; auto.
  intuition.
  intuition.
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
  induction 1 using typ_wf_mut with
  (P := fun G t T => fun H : G |-= t : T =>
  forall U V, (T = Prod U V \/ T = Sum U V) -> type_no_kind T)
  (P0 := fun e => fun H : wf e => 
    forall T n, item_lift T e n -> 
    forall U V, (T = Prod U V \/ T = Sum U V) -> type_no_kind T)
 ; simpl ; intros ; auto with coc ; try discriminate ; 
 try (destruct H ; discriminate) ;  try (destruct H1 ; discriminate).

  apply IHtyp with n U V ; auto.

  destruct H2 ; try discriminate.
  assert (e |-= Prod T U : Srt s2).
  apply type_prod with s1 ; auto with coc.
  pose (type_has_no_kind H3) ; auto with coc.

  destruct H1.
  induction Ur ;  try (unfold subst, subst_rec ; simpl ; intros ; discriminate).
  unfold subst in H1.
  generalize H1 ; clear H1.
  unfold subst_rec ; elim (lt_eq_lt_dec 0 n).
  intro a ; case a ; clear a ; intros ; try discriminate.
  rewrite <- e0 ; simpl.
  unfold subst ; simpl.
  rewrite lift0.
  apply (type_has_no_kind H) ; auto with coc.

  intros ; discriminate.
  pose (IHtyp2 V (Prod Ur1 Ur2) (or_introl _ (refl_equal (Prod V (Prod Ur1 Ur2))))).
  simpl in t.
  destruct t.
  destruct H3.
  unfold subst in H1 ; simpl in H1.
  clear IHUr1 IHUr2.

  inversion H1.

  pose (type_has_no_kind H).
  split ; apply type_range_subst_not_kind ; auto.

  induction Ur ;  try (unfold subst, subst_rec ; simpl ; intros ; discriminate).
  unfold subst in H1.
  generalize H1 ; clear H1.
  unfold subst_rec ; elim (lt_eq_lt_dec 0 n).
  intro a ; case a ; clear a ; intros ; try discriminate.
  rewrite <- e0 ; simpl.
  unfold subst ; simpl.
  rewrite lift0.
  apply (type_has_no_kind H) ; auto with coc.

  intros ; discriminate.
  pose (IHtyp2 V (Sum Ur1 Ur2) (or_introl _ (refl_equal (Prod V (Sum Ur1 Ur2))))).
  simpl in t.
  destruct t.
  destruct H3.
  unfold subst in H1 ; simpl in H1.
  clear IHUr1 IHUr2.

  inversion H1.

  pose (type_has_no_kind H).
  split ; apply type_range_subst_not_kind ; auto.

  destruct H3.
  discriminate.
  inversion H3.
  rewrite <- H6.
  rewrite <- H5.
  split ; [apply (type_has_no_kind H) | apply (type_has_no_kind H1)].
  
  pose (IHtyp U V (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0.
  intuition.
  
  assert(type_no_kind (Pi1 t)) ; auto with coc.
  simpl ; auto.
  unfold subst ; apply type_range_subst_not_kind ; auto.
  intuition.
  pose (IHtyp U V (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0 ; intuition.
  pose (IHtyp U V (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0 ; intuition.
    
(*  induction M ; intuition ; try discriminate.
  generalize H4 ; unfold subst, subst_rec.
  elim (lt_eq_lt_dec 0 n) ; intros a ; try discriminate.
  case a ; clear a ; intros ; try discriminate.
  rewrite lift0. rewrite lift0 in H3.
  rewrite H3 ; rewrite H3 in H.
  pose (type_has_no_kind H) ; auto with coc.
  
  intros ; discriminate.
  pose (type_has_no_kind H2).
  pose (type_has_no_kind H).
  unfold subst ; apply type_range_subst_not_kind ; auto.
  
  unfold subst in H4 ; simpl in H4.
  inversion H4.
  pose (type_has_no_kind H2).
  pose (type_has_no_kind H).
  unfold subst ; apply type_range_subst_not_kind ; auto.

  unfold subst in H4 ; simpl in H4.
  inversion H4.
  pose (type_has_no_kind H2).
  pose (type_has_no_kind H).
  unfold subst ; apply type_range_subst_not_kind ; auto.*)
  
  destruct H2 ;
  rewrite H2 in H0 ;
  rewrite H2 ; apply (type_has_no_kind H0).

  destruct H.
  elim (inv_nth_nl _ _ _ H1).
  
  assert (wf (T :: e)). 
  apply wf_var with s ; auto with coc.
  destruct (wf_sort_lift H2 H0).
  apply (type_has_no_kind H3).
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
 