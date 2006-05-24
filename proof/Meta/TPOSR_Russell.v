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

Require Import Russell.Types.
Require Import Russell.UnicityOfSorting.

Require Import TPOSR.Terms.
Require Import TPOSR.Reduction.
Require Import TPOSR.Conv.
Require Import TPOSR.LiftSubst.
Require Import TPOSR.Env.
Require Import TPOSR.Types.
Require Import TPOSR.Unlab.

Require Import Meta.JRussell_Russell.
Require Import Meta.TPOSR_JRussell.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Set Implicit Arguments.

Theorem tposr_russell : forall G M N A, G |- M -> N : A ->
  (unlab_ctx G) |- (|M|) : (|A|) /\ (unlab_ctx G) |- (|N|) : (|A|).
Proof.
  intros.
  pose (unlab_sound_type H).
  destruct (validity_jeq j).
  destruct H0.
  split ; apply type_jrussell_to_russell ; auto.
Qed.

Theorem tposr_eq_russell : forall G M N s, G |- M ~= N : s ->
  (unlab_ctx G) |- (|M|) : Srt s /\ (unlab_ctx G) |- (|N|) : Srt s.
Proof.
  induction 1 ; simpl ; intros.

  apply (tposr_russell H).

  intuition.
  
  intuition.
Qed.

Theorem tposr_unique_sort : forall G A B C s s', G |- A -> B : Srt_l s -> G |- A -> C : Srt_l s' ->
  s = s'.
Proof.
  intros.
  destruct (tposr_russell H).
  destruct (tposr_russell H0).
  simpl in H1 ; simpl in H3.
  apply (unique_sort H1 H3).
Qed.

Theorem tposr_eq_unique_sort : forall G A B C s s', G |- A ~= B : s -> G |- A ~= C : s' ->
  s = s'.
Proof.
  simpl ; intros.

  destruct (tposr_eq_russell H).
  destruct (tposr_eq_russell H0).
  apply (unique_sort H1 H3).
Qed.
