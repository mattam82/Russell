Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import JRussell.Types.
Require Import JRussell.Coercion.
Require Import JRussell.Substitution.

Require Import Coq.Arith.Arith.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Lemma pre_functionality_rec : forall g (d : term) t, g |- d : t -> forall d', g |- d = d' : t ->
  forall e U T, e |- U : T ->
  forall f n, sub_in_env d t n e f -> trunc _ n f g -> 
  f |- (subst_rec d U n) = (subst_rec d' U n) : (subst_rec d T n).
Proof.
  intros g d t H d' Heq.
  induction 1 ; simpl ; intros ; auto with coc arith ; try simpl in IHjeq1 ; try simpl in IHjeq2 
  ; try simpl in IHjeq3 ; try simpl in IHjeq4.

  inversion H0.

  inversion H0.

  elim (lt_eq_lt_dec n 0).
  destruct a.
  elim (lt_n_O _ l).
  rewrite e0 in H2.
  inversion H2.
  rewrite e0.
  rewrite simpl_subst ; auto with arith ; do 3 rewrite lift0.
  rewrite e0 in H1.
  inversion H1.
  rewrite <- H3.
  assumption.

  intros.
  apply jeq_refl ; auto.
  inversion H1.
  rewrite <- H3 in b.
  elim (lt_n_O _ b).
  rewrite <- H4 in H2.
  inversion H2.
  rewrite commut_lift_subst.
  
  apply type_var with s ; auto.
  change (Srt s) with (subst_rec d (Srt s) n0).
  apply typ_sub_weak with g t e ; auto.
  rewrite <- H5 in H10.
  inversion H10.
  rewrite <- H14.
  assumption.

  inversion H0.
  rewrite <- H2 in H1.
  inversion H1.
  do 3 (rewrite simpl_subst ; auto with arith).
  do 2 rewrite lift0.
  apply jeq_refl ; auto.
  rewrite <- H8.
  rewrite <- H3 ; assumption.
  rewrite <- H3 in H1.
  rewrite <- H4 in H1.
  inversion H1.
  
  do 3 rewrite commut_lift_subst.
  apply jeq_weak with s; auto.
  change (Srt s) with (subst_rec d (Srt s) n0).
  apply typ_sub_weak with g t e ; auto.
  
  apply jeq_abs with s1 s2 ; auto with coc.
  change (Srt s1) with (subst_rec d (Srt s1) n) ; auto with coc.
  change (Srt s2) with (subst_rec d (Srt s2) (S n)) ; auto with coc.
  apply typ_sub_weak with g t (T :: e) ; try constructor ; auto.
  
  rewrite distr_subst.
  apply jeq_app with (subst_rec d V n) ; auto with coc.
  simpl in IHtyp2 ; apply IHtyp2 ; auto with coc ; try constructor ; auto with coc.

  apply jeq_pair with s1 s2 s3 ; auto with coc.
  change (Srt s1) with (subst_rec d (Srt s1) n) ; auto with coc.
  change (Srt s2) with (subst_rec d (Srt s2) (S n)) ; auto with coc.
  rewrite <- distr_subst.
  apply IHtyp4 ; auto with coc.

  simpl in IHtyp1 ; simpl in IHtyp2.
  apply jeq_prod with s1 ; auto with coc.

  simpl in IHtyp1 ; simpl in IHtyp2.
  apply jeq_sum with s1 s2 ; auto with coc.

  simpl in IHtyp1 ; simpl in IHtyp2.
  apply jeq_subset ; auto with coc.

  simpl in IHtyp.
  apply jeq_pi1 with (subst_rec d V (S n)) ; auto with coc.

  simpl in IHtyp.
  rewrite distr_subst.
  simpl.
  apply jeq_pi2 with (subst_rec d U n) ; auto with coc.

  pose (IHtyp _ _ H2 H3).
  apply jeq_conv with (subst_rec d U n) s ; auto with coc.
  apply coerce_sub_weak with g t e ; auto with coc.
Qed.

Lemma pre_functionality : forall e (d : term) t, e |- d : t -> 
  forall d', e |- d = d' : t ->
  forall U T, t :: e |- U : T ->
  e |- (subst d U) = (subst d' U) : (subst d T).
Proof.
  intros.
  unfold subst ; pose pre_functionality_rec.
  apply (@pre_functionality_rec e d t H d' H0 (t :: e) U T H1).
  constructor.
  constructor.
Qed.

