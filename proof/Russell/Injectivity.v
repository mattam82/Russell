Require Import Lambda.Tactics.
Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.Russell.Types.
Require Import Lambda.Russell.Thinning.
Require Import Lambda.Russell.Substitution.
Require Import Lambda.Russell.Coercion.
Require Import Lambda.Russell.GenerationNotKind.
Require Import Lambda.Russell.GenerationCoerce.
Require Import Lambda.Russell.Generation.

Require Import Lambda.Meta.Russell_TPOSR.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Lemma unique_sort_conv : forall G A A' s1 s2, G |-- A : Srt s1 -> G |-- A' : Srt s2 -> conv A A' -> s1 = s2.
Proof.
  apply russell_unique_sort_conv.
Qed.

Lemma inv_conv_prod_sort_l : forall e U V U' V' s, e |-- Prod U V : Srt s -> e |-- Prod U' V' : Srt s ->
  conv (Prod U V) (Prod U' V') -> exists s1 : sort, e |-- U : Srt s1 /\ e |-- U' : Srt s1 .
Proof.
  intros.
  destruct (generation_prod2 H).
  destruct (generation_prod2 H0).
  destruct H2 ; destruct H4.
  pose (inv_conv_prod_l _ _ _ _ H1).
  pose (inv_conv_prod_r _ _ _ _ H1).
  pose (unique_sort_conv H2 H4 c).
  exists x.
  split ; intuition.
  rewrite e0 ; assumption.
Qed.

Lemma inv_conv_prod_sort_r : forall e U V U' V' s, e |-- Prod U V : Srt s -> e |-- Prod U' V' : Srt s ->
  conv (Prod U V) (Prod U' V') -> U' :: e |-- V : Srt s /\ U' :: e |-- V' : Srt s. 
Proof.
  intros.
  destruct (generation_prod2 H).
  destruct (generation_prod2 H0).
  destruct H2 ; destruct H4.
  pose (inv_conv_prod_l _ _ _ _ H1).
  pose (inv_conv_prod_r _ _ _ _ H1).
  pose (unique_sort_conv H2 H4 c).
  intuition.
  apply typ_conv_env with (U :: e) ; auto with coc.
  apply coerce_env_hd with x0.
  apply coerce_conv with U' U'; auto with coc.
  rewrite <- e0 ; auto.
  apply wf_var with x0 ; auto.
Qed.

Lemma inv_conv_sum_sort : forall e U V U' V' s, e |-- Sum U V : Srt s -> e |-- Sum U' V' : Srt s ->
  conv (Sum U V) (Sum U' V') -> 
  exists s1, exists s2, e |-- U : Srt s1 /\ e |-- U' : Srt s1 /\ U :: e |-- V : Srt s2 /\ U :: e |-- V' : Srt s2
  /\ sum_sort s1 s2 s.	
Proof. 
  intros.
  destruct (generation_sum2 H).
  destruct (generation_sum2 H0).
  pose (generation_sum H).
  destruct H3 ; destruct e0 ; destruct H5.
  intuition.
  pose (inv_conv_sum_l _ _ _ _ H1).
  pose (inv_conv_sum_r _ _ _ _ H1).
  exists s ; exists s ; intuition.

  apply typ_conv_env with (U' :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  apply wf_var with s ; auto with coc.
Qed.

Require Import Lambda.Russell.UnicityOfSorting.

(** Versions of the lemmas usable when in Set *)
Lemma inv_conv_prod_sort_l_set : forall e U V U' V' s, 
  e |-- Prod U V : Srt s -> e |-- Prod U' V' : Srt s ->
  conv (Prod U V) (Prod U' V') -> 
  forall s1, e |-- U : Srt s1 -> e |-- U' : Srt s1.
Proof.
  intros.
  destruct (inv_conv_prod_sort_l H H0 H1).
  destruct_exists.
  rewrite (unique_sort H2 H3) ; auto.
Qed.


Lemma inv_conv_prod_sort_r_set : forall e U V U' V' s, 
  e |-- Prod U V : Srt s -> e |-- Prod U' V' : Srt s ->
  conv (Prod U V) (Prod U' V') -> 
  U' :: e |-- V : Srt s /\ U' :: e |-- V' : Srt s. 
Proof.
  intros.
  destruct (inv_conv_prod_sort_r H H0 H1).
  intuition.
Qed.

Lemma inv_conv_sum_sort_l_set : forall e U V U' V' s, e |-- Sum U V : Srt s -> e |-- Sum U' V' : Srt s ->
  conv (Sum U V) (Sum U' V') -> 
  forall s1 : sort, e |-- U : Srt s1 -> e |-- U' : Srt s1.
Proof.
  intros.
  destruct (inv_conv_sum_sort H H0 H1).
  destruct_exists.
  rewrite (unique_sort H2 H3) ; auto.
Qed.

Lemma inv_conv_sum_sort_r_set : forall e U V U' V' s, e |-- Sum U V : Srt s -> e |-- Sum U' V' : Srt s ->
  conv (Sum U V) (Sum U' V') -> 
  forall s2 : sort, U :: e |-- V : Srt s2 -> U :: e |-- V' : Srt s2.
Proof.
  intros.
  destruct (inv_conv_sum_sort H H0 H1).
  destruct_exists.
  rewrite (unique_sort H2 H5) ; auto.
Qed.
