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

(*  
Require Import Lambda.TPOSR.Basic.

Theorem tposr_coerce_russell_coerce : forall G M N s, G |-- M >-> N : s ->
  unlab_ctx G |-- (|M|) >> (|N|) : s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  pose (tposr_eq_russell H) ; destruct_exists.
  apply coerce_conv with (|A|) (|A|) ; auto with coc.
  pose (tposr_eq_conv H).
  apply conv_unlab_conv ; auto.

  pose (tposr_coerce_russell H) ; destruct_exists.
  pose (tposr_coerce_russell H2) ; destruct_exists.
  apply coerce_prod with s ; auto with coc.
  pose (tposr_russell H3) ; destruct_exists.
  assumption.

  pose (tposr_coerce_russell H) ; destruct_exists.
  pose (tposr_coerce_russell H2) ; destruct_exists.
  apply coerce_sum with s s' ; auto with coc.
  pose (tposr_russell H4) ; destruct_exists.
  assumption.

  pose (tposr_coerce_russell H) ; destruct_exists.
  apply coerce_sub_l ; auto with coc.
  pose (tposr_russell H2) ; destruct_exists.
  assumption.

  pose (tposr_coerce_russell H) ; destruct_exists.
  apply coerce_sub_r ; auto with coc.
  pose (tposr_russell H2) ; destruct_exists.
  assumption.
Admitted.
*)
Theorem tposr_unique_sort : forall G A B C s s', G |-- A -> B : Srt_l s -> G |-- A -> C : Srt_l s' ->
  s = s'.
Proof.
  intros.
  destruct (tposr_russell H).
  destruct (tposr_russell H0).
  simpl in H1 ; simpl in H3.
  apply (unique_sort H1 H3).
Qed.

Theorem tposr_eq_unique_sort : forall G A B C s s', G |-- A ~= B : s -> G |-- A ~= C : s' ->
  s = s'.
Proof.
  simpl ; intros.

  destruct (tposr_eq_russell H).
  destruct (tposr_eq_russell H0).
  apply (unique_sort H1 H3).
Qed.

Theorem tposr_coerce_unique_sort : forall G A B C s s', G |-- A >-> B : s -> G |-- A >-> C : s' ->
  s = s'.
Proof.
  simpl ; intros.

  destruct (tposr_coerce_russell H).
  destruct (tposr_coerce_russell H0).
  apply (unique_sort H1 H3).
Qed.
