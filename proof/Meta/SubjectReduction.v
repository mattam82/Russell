Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.MyList.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.SubjectReduction.
Require Import Lambda.TPOSR.Unlab.

Require Import Lambda.Meta.TPOSR_JRussell.
Require Import Lambda.Meta.JRussell_Russell.
Require Import Lambda.Meta.Russell_JRussell.
Require Import Lambda.Meta.Russell_TPOSR.

Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.

Require Import Lambda.JRussell.Types.
Require Import Lambda.JRussell.Validity.

Set Implicit Arguments.

Lemma jrussell_subject_reduction : 
  forall e t T, e |-= t : T -> forall u, red t u -> 
  e |-= t = u : T.
Proof.
  intros.
  pose (type_jrussell_to_russell _ _ _ H). 
  pose (type_russell_tposr t0) ; destruct_exists.
  subst.
  pose (unlab_lab_red _ H0) ; destruct_exists.
  assert(par_lred b x) by (apply lred_par_lred ; auto).
  assert(tposr_term a b c) by eauto with coc.
  rewrite <- H1.
  apply unlab_sound_tposrp.
  apply (subject_reduction_p H3 H5).
Qed.

Require Import Lambda.Russell.Types.

Lemma russell_subject_reduction : 
  forall e t T, e |-- t : T -> forall u, red t u -> 
  e |-- u : T.
Proof.
  intros.
  pose (type_russell_jrussell H).
  pose (jrussell_subject_reduction t0 H0).
  pose (jeq_type_r j).
  apply (type_jrussell_to_russell _ _ _ t1).
Qed.