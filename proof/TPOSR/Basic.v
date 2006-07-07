Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Thinning.
Require Import Lambda.TPOSR.CtxReduction.
Require Import Lambda.TPOSR.CtxExpansion.
Require Import Lambda.TPOSR.CtxCoercion.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.SubstitutionTPOSR.
Require Import Lambda.TPOSR.RightReflexivity.

Set Implicit Arguments.

Lemma tposr_conv_eq : forall e A B s, e |-- A ~= B : s -> 
  forall M N, (e |-- M -> N : A -> e |-- M -> N : B) /\ (e |-- M -> N : B -> e |-- M -> N : A).
Proof.
  induction 1 ; simpl ; intros.
  
  split ; intros.
  apply tposr_conv with X s ; eauto with coc ecoc.
  apply tposr_coerce_conv.
  apply tposr_conv with Y s ; auto with coc.

  pose (IHtposr_eq M N).
  intuition ; auto with coc.

  pose (IHtposr_eq1 M N).
  pose (IHtposr_eq2 M N).
  intuition ; auto with coc.
Qed.

Corollary tposr_conv_l : forall e A B s, e |-- A ~= B : s -> 
  forall M N, e |-- M -> N : A -> e |-- M -> N : B.
Proof.
  intros.
  exact ((proj1 (tposr_conv_eq H M N)) H0).
Qed.

Corollary tposr_conv_r : forall e A B s, e |-- A ~= B : s -> 
  forall M N, e |-- M -> N : B -> e |-- M -> N : A.
Proof.
  intros.
  exact ((proj2 (tposr_conv_eq H M N)) H0).
Qed.

Corollary tposrp_conv_l : forall e A B s, e |-- A ~= B : s -> 
  forall M N, e |-- M -+> N : A -> e |-- M -+> N : B.
Proof.
  intros.
  induction H0.
  apply tposrp_tposr.
  exact ((proj1 (tposr_conv_eq H X Y)) H0).

  pose (IHtposrp1 H).
  pose (IHtposrp2 H).
  eauto with ecoc.
Qed.

Corollary tposrp_conv_r : forall e A B s, e |-- A ~= B : s -> 
  forall M N, e |-- M -+> N : B -> e |-- M -+> N : A.
Proof.
  intros.
  induction H0.
  apply tposrp_tposr.
  exact ((proj2 (tposr_conv_eq H X Y)) H0).

  eauto with ecoc.
Qed.

Lemma tposrp_conv : forall e A B s, e |-- A >-> B : s -> 
  forall M N, e |-- M -+> N : A -> e |-- M -+> N : B.
Proof.
  intros.
  induction H0.
  apply tposrp_tposr.
  apply tposr_conv with Z s ; auto with coc.

  pose (IHtposrp1 H).
  pose (IHtposrp2 H).
  eauto with ecoc.
Qed.


Lemma tposrp_tposr_eq_aux : forall e M N Z, e |-- M -+> N : Z -> forall s, Z = Srt_l s -> e |-- M ~= N : s.
Proof.
  induction 1 ; simpl ; intros ; eauto with coc.
  apply tposr_eq_tposr.
  rewrite <- H0 ; assumption.
  pose (IHtposrp1 _ H1).
  pose (IHtposrp2 _ H1).
  apply tposr_eq_trans with X ; auto.
Qed.

Lemma tposrp_tposr_eq : forall e M N s, e |-- M -+> N : Srt_l s -> e |-- M ~= N : s.
Proof.
  intros ; eapply tposrp_tposr_eq_aux ; auto ; auto.
Qed.

Hint Resolve tposrp_tposr_eq : coc.

Lemma context_validity : forall g, tposr_wf g -> forall n d, trunc _ n g d -> tposr_wf d.
Proof.
  induction g  ; simpl ; auto with coc.
  intros.
  inversion H0 ; auto with coc.

  intros.
  inversion H.
  pose (wf_tposr H2).
  inversion H0.
  rewrite H6 in H0.
  apply wf_cons with A' s ; auto with coc.
  rewrite <- H5 in H0.
  apply (IHg t) with k  ; auto.
Qed.

Lemma tposr_not_kind_aux : forall e t u T, tposr e t u T -> t <> Srt_l kind.
Proof.
  induction 1 ; simpl ; red ; intros ; try discriminate.
  contradiction.
Qed.

Lemma tposr_not_kind : forall e u T, ~ tposr e (Srt_l kind) u T.
Proof.
  intros.
  red ; intros ; apply (tposr_not_kind_aux H) ; auto.
Qed.

Hint Resolve tposr_not_kind : coc.

Lemma lsubst_to_sort : forall M N s, lsubst M N = Srt_l s -> or (M = Srt_l s) (N = Srt_l s).
Proof.
  induction N ; simpl ; intros ; try discriminate.
  unfold lsubst in H ; simpl in H.
  inversion H.
  right ; auto.

  left.
  generalize H ; clear H.
  case n.
  simpl ; intros.
  unfold lsubst in H ; simpl in H.
  rewrite llift0 in H.
  assumption.
  intros.
  unfold lsubst in H ; simpl in H.
  discriminate.
Qed.


