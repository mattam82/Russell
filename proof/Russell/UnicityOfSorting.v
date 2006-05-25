Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Conv_Dec.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Russell.Types.
Require Import Russell.Thinning.
Require Import Russell.Substitution.
Require Import Russell.Coercion.
Require Import Russell.GenerationNotKind.
Require Import Russell.GenerationCoerce.
Require Import Russell.Generation.
Require Import Russell.GenerationRange.
Require Import Russell.UnicityOfSortingRange.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.


Theorem unique_sort : forall t e s s', 
  e |-- t : (Srt s) -> e |-- t : (Srt s') -> s = s'.
Proof.
  intros.
  exact (unique_range_sort H H0 (refl_equal (Srt s)) (refl_equal (Srt s'))).
Qed.

Lemma any_sort_coerce_l : forall e U V s, e |-- U >> V : s -> forall s',
  e |-- U : Srt s' -> e |-- U >> V : s'.
Proof.
  intros.
  pose (coerce_sort_l H).
  rewrite <- (unique_sort t H0).
  assumption.
Qed.

Lemma any_sort_coerce_r : forall e U V s, e |-- U >> V : s -> forall s',
  e |-- V : Srt s' -> e |-- U >> V : s'.
Proof.
  intros.
  pose (coerce_sort_r H).
  rewrite <- (unique_sort t H0).
  assumption.
Qed.