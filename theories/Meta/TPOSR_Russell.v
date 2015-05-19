Require Import Lambda.Tactics.
Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.

Require Import Lambda.JRussell.Types.
Require Import Lambda.JRussell.Basic.
Require Import Lambda.JRussell.Generation.
Require Import Lambda.JRussell.Thinning.
Require Import Lambda.JRussell.Validity.

Require Import Lambda.Russell.Types.
Require Import Lambda.Russell.UnicityOfSorting.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Unlab.

Require Import Lambda.Meta.JRussell_Russell.
Require Import Lambda.Meta.TPOSR_JRussell.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Set Implicit Arguments.

Theorem tposr_russell : forall G M N A, G |-- M -> N : A ->
  (unlab_ctx G) |-- (|M|) : (|A|) /\ (unlab_ctx G) |-- (|N|) : (|A|).
Proof.
  intros.
  pose (unlab_sound_type H).
  destruct (validity_jeq j).
  destruct H0.
  split ; apply type_jrussell_to_russell ; auto.
Qed.

Theorem tposr_eq_russell : forall G M N s, G |-- M ~= N : s ->
  (unlab_ctx G) |-- (|M|) : Srt s /\ (unlab_ctx G) |-- (|N|) : Srt s.
Proof.
  induction 1 ; simpl ; intros.

  apply (tposr_russell H).

  intuition.
  
  intuition.
Qed.

Theorem tposr_coerce_russell : forall G M N s, G |-- M >-> N : s ->
  (unlab_ctx G) |-- (|M|) : Srt s /\ (unlab_ctx G) |-- (|N|) : Srt s.
Proof.
  induction 1 ; simpl ; intros ; try solve [ intuition ; intros ; auto with coc].
  
  apply (tposr_eq_russell H).

  intuition.
  apply type_prod with s ; auto with coc.
  destruct (tposr_russell H3).
  auto.
  apply type_prod with s ; auto with coc.

  intuition.
  apply type_sum with s s' ; auto with coc.
  apply type_sum with s s' ; auto with coc.
  destruct (tposr_russell H4).
  auto.

  intuition.
  apply type_subset ; auto with coc.
  destruct (tposr_russell H2) ; auto.

  intuition.
  apply type_subset ; auto with coc.
  destruct (tposr_russell H2) ; auto.
Qed.
