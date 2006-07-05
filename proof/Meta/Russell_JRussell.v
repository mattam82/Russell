Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.MyList.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.SubjectReduction.
Require Import Lambda.TPOSR.Unlab.

Require Import Lambda.Meta.Russell_TPOSR.
Require Import Lambda.Meta.TPOSR_JRussell.

Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Russell.Types.

Require Import Lambda.JRussell.Types.
Require Import Lambda.JRussell.Validity.

Set Implicit Arguments.

Lemma type_russell_jrussell : forall e t T, e |-- t : T -> e |-= t : T.
Proof.
  intros.
  pose (type_russell_tposr H) ; destruct_exists.
  pose (unlab_sound_type H3).
  subst.
  apply (jeq_type_l j).
Qed.

Lemma conv_russell_jrussell : forall e t u T, 
  e |-- t : T -> e |-- u : T -> conv t u ->
  e |-= t = u : T.
Proof.
  intros.
  destruct (church_rosser _ _ H1).
  pose (type_russell_tposr H) ; pose (type_russell_tposr H0) ; destruct_exists.
  subst.
  pose (unlab_lab_red _ H2) ; pose (unlab_lab_red _ H3) ; destruct_exists.
  subst.
  assert(tposr_term a b c) by eauto with coc ecoc.
  assert(tposr_term a0 b0 c0) by eauto with coc ecoc.
  assert(a |-- b -+> x0 : c). 
  apply subject_reduction_p ; auto with coc.
  assert(a0 |-- b0 -+> x1 : c0). 
  apply subject_reduction_p ; auto with coc.
  pose (unlab_sound_tposrp H13).
  pose (unlab_sound_tposrp H14).
  rewrite H5 in j.
  apply jeq_trans with (|x1|) ; auto with coc.
  rewrite <- H4 ; rewrite <- H7 ; auto with coc.
Qed.


Require Import Lambda.Meta.JRussell_Russell.

Theorem russell_equiv_jrussell_type : 
  forall e t T, e |-= t : T <-> e |-- t : T.
Proof.
  intros ; split.
  apply type_jrussell_to_russell.
  apply type_russell_jrussell.
Qed.

Theorem russell_equiv_jrussell_conv : 
  forall e t u T, e |-= t = u : T <-> (e |-- t : T /\ e |-- u : T /\ conv t u).
Proof.
  intros ; split.
  intros H.
  apply (jeq_jrussell_to_russell _ _ _ _ H).
  intros ; intuition.
  apply conv_russell_jrussell ; auto.
Qed.
