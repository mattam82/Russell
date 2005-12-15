Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import CCP.Types.

Lemma refl_coerce : forall U, U >> U.
Proof.
  intros.
  apply coerce_conv ; auto with coc core.
Qed.

Lemma coerce_conv_coerce : forall U U' V V', conv U U' -> conv V V' ->
  U >> V -> U' >> V'.
Proof.
intros.
induction H1 ; auto with coc core.
apply coerce_conv.
apply trans_conv_conv with A ; auto with coc.
apply trans_conv_conv with B ; auto with coc.

apply coerce_trans with (Prod A' B') ; auto with coc core.
apply coerce_trans with (Prod A B) ; auto with coc core.

apply coerce_trans with (Sum A' B') ; auto with coc core.
apply coerce_trans with (Sum A B) ; auto with coc core.

apply coerce_trans with (Subset U P) ; auto with coc core.
apply coerce_sub_l ; auto with coc core.
apply coerce_trans with U'0 ; auto with coc core.

apply coerce_trans with (Subset U'0 P) ; auto with coc core.
apply coerce_sub_r ; auto with coc core.
apply coerce_trans with U ; auto with coc core.

apply coerce_trans with A ; auto with coc core.
apply coerce_trans with B ; auto with coc core.
apply coerce_trans with C ; auto with coc core.
Qed.

Lemma sym_coerce : forall U V, U >> V -> V >> U.
Proof.
intros.
induction H ; auto with coc.

apply coerce_trans with B ; auto with coc.
Qed.

Lemma coerce_subst_rec : forall U V,  U >> V -> forall u v, conv u v -> forall n, subst_rec u U n >> subst_rec v V n.
Proof.
  induction 1 ; intros ; simpl.
  apply coerce_conv ; auto with coc.
 
 apply coerce_prod ; auto with coc.

 apply coerce_sum ; auto with coc.

 apply coerce_sub_l ; auto with coc.

 apply coerce_sub_r ; auto with coc.

 apply coerce_trans with (subst_rec u B n) ; auto with coc.
Qed.

Lemma subst_coerce : forall U V, U >> V -> forall t, subst t U >> subst t V.
Proof.
  intros.
  unfold subst ; apply coerce_subst_rec ; auto with coc.
Qed.

Lemma coerce_lift_rec : forall U V,  U >> V -> forall n k, lift_rec k U n >> lift_rec k V n.
Proof.
  induction 1 ; intros ; simpl.
  apply coerce_conv ; auto with coc.
 
 apply coerce_prod ; auto with coc.

 apply coerce_sum ; auto with coc.

 apply coerce_sub_l ; auto with coc.

 apply coerce_sub_r ; auto with coc.

 apply coerce_trans with (lift_rec k B n) ; auto with coc.
Qed.

Lemma lift_coerce : forall U V, U >> V -> forall n, lift n U >> lift n V.
Proof.
  intros.
  unfold lift ; apply coerce_lift_rec ; auto with coc.
Qed.

Hint Resolve refl_coerce sym_coerce subst_coerce lift_coerce : coc.
