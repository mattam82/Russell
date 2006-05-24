Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.

Require Import JRussell.Types.
Require Import JRussell.Basic.
Require Import JRussell.Generation.
Require Import JRussell.Thinning.
Require Import JRussell.Validity.

Require Import TPOSR.Terms.
Require Import TPOSR.Reduction.
Require Import TPOSR.Conv.
Require Import TPOSR.LiftSubst.
Require Import TPOSR.Env.
Require Import TPOSR.Types.
Require Import TPOSR.Unlab.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Set Implicit Arguments.

Lemma item_unlab : forall n t e, item lterm t e n -> item term (|t|) (unlab_ctx e) n.
Proof.
  induction n ; simpl ; intros ; auto.
  inversion H.
  simpl.
  constructor.
  
  inversion H.
  simpl.
  constructor.
  apply IHn ; auto.
Qed.

Theorem unlab_sound  : 
  (forall e u v T, e |- u -> v : T -> 
  (unlab_ctx e) |- (|u|) = (|v|) : (|T|)) /\
  (forall e, tposr_wf e -> 
  (unlab_ctx e) |- Srt prop : Srt kind /\
  (unlab_ctx e) |- Srt set : Srt kind /\
  (forall A n, item_llift A e n -> 
  (unlab_ctx e) |- Ref n : (|A|))).
Proof.
  apply ind_tposr_wf with 
  (P := fun e u v T=>  fun H : e |- u -> v : T =>
  (unlab_ctx e) |- (|u|) = (|v|) : (|T|))
  (P0 := fun e => fun H : tposr_wf e =>
  (unlab_ctx e) |- Srt prop : Srt kind /\
  (unlab_ctx e) |- Srt set : Srt kind /\
  (forall A n, item_llift A e n -> 
  (unlab_ctx e) |- Ref n : (|A|))) ; simpl ; intros ; auto with coc.

  intuition.

  intuition.

  intuition.

  apply jeq_prod with s1 ; auto with coc.

  apply jeq_abs with s1 s2 ; auto with coc.
  apply (jeq_type_l H0).

  rewrite lab_subst.
  apply jeq_app with (|A|) ; auto.

  do 2 rewrite lab_subst.
  pose (jeq_type_l H).
  pose (jeq_type_l H0).
  pose (jeq_type_l H1).
  pose (jeq_type_l H2).
  
  apply jeq_trans with (subst (|N |) (|M |)) ; auto with coc.
  apply jeq_beta with s1 s2 ; auto with coc.
  
  apply jeq_subst_par with (|A|); auto with coc.

  apply jeq_red with (|A|) s ; auto with coc.

  apply jeq_exp with (|B|) s ; auto with coc.

  apply jeq_subset ; auto with coc.

  apply jeq_sum  with s1 s2 ; auto with coc.

  apply jeq_pi1 with (|B|) ; auto with coc.

  pose (jeq_type_l H).
  pose (jeq_type_l H0).
  pose (jeq_type_l H1).
  pose (generation_pair t4).
  destruct e0.
  do 4 destruct H2.
  intuition.
  inversion H3.
  apply jeq_pi1_red with s1 s2 s3 ; auto with coc.
  rewrite H10 ; assumption.
  rewrite H11 ; assumption.

  rewrite lab_subst.
  simpl.
  apply jeq_pi2 with (|A|) ; auto with coc.

  pose (jeq_type_l H).
  pose (jeq_type_l H0).
  pose (jeq_type_l H1).
  pose (generation_pair t4).
  destruct e0.
  do 4 destruct H2.
  intuition.
  inversion H3.
  rewrite lab_subst.
  apply jeq_pi2_red with s1 s2 s3 ; auto with coc.
  rewrite H10 ; assumption.
  rewrite H11 ; assumption.

  split ; auto with coc.
  split ; auto with coc.
  intros.
  inversion H.
  inversion H1.

  split ; auto with coc.
  apply sort_judgement_empty_env ; auto with coc.
  apply consistent_cons with s ; auto with coc.
  apply (jeq_consistent H).
  apply (jeq_type_l H).

  split.
  apply sort_judgement_empty_env ; auto with coc.
  apply consistent_cons with s ; auto with coc.
  apply (jeq_consistent H).
  apply (jeq_type_l H).

  intros.
  inversion H0.
  rewrite H1.
  rewrite lab_lift.
  apply (item_ref_lift).
  induction n.
  inversion H2.
  constructor.
  constructor.
  inversion H2.
  apply (item_unlab H4).
  
  apply consistent_cons with s.
  apply (jeq_consistent H).
  apply (jeq_type_l H).
Qed.

Corollary unlab_sound_type : forall e u v T, e |- u -> v : T -> 
  (unlab_ctx e) |- (|u|) = (|v|) : (|T|).
Proof (proj1 (unlab_sound)).

Corollary unlab_sound_wf :
  (forall e, tposr_wf e -> 
  (unlab_ctx e) |- Srt prop : Srt kind /\
  (unlab_ctx e) |- Srt set : Srt kind /\
  (forall A n, item_llift A e n -> 
  (unlab_ctx e) |- Ref n : (|A|))).
Proof (proj2 (unlab_sound)).


