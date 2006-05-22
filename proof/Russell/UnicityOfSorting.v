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
  e |- t : (Srt s) -> e |- t : (Srt s') -> s = s'.
Proof.
  intros.
  exact (unique_range_sort H H0 (refl_equal (Srt s)) (refl_equal (Srt s'))).
Qed.
(*
Theorem uniqueness_of_types : forall G t T, G |- t : T ->
  forall T', G |- t : T' ->
  (exists s, T = Srt s /\ T = T') \/ (exists s', G |- T >> T' : s').
Proof.
  induction t ; simpl ; intros.
  
  pose (typ_sort H0).
  pose (typ_sort H).
  left ; exists kind ; intuition.
  rewrite H2 ; rewrite H4 ; auto.


  Focus 2.
  pose (unique_var

  left ; exists kind ; intuition ; auto.
  pose (typ_sort H0).
  left ; exists kind ; intuition ; auto.
  
  destruct (wf_sort_lift H H0).
  
*)