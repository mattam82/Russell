Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Conv_Dec.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.JRussell.Types.
Require Import Lambda.JRussell.Thinning.
Require Import Lambda.JRussell.Substitution.
Require Import Lambda.JRussell.Coercion.
Require Import Lambda.JRussell.GenerationNotKind.
Require Import Lambda.JRussell.GenerationCoerce.
Require Import Lambda.JRussell.Generation.
Require Import Lambda.JRussell.GenerationRange.
Require Import Lambda.JRussell.UnicityOfSortingRange.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.


Theorem unique_sort : forall t e s s', 
  e |-= t : (Srt s) -> e |-= t : (Srt s') -> s = s'.
Proof.
  intros.
  exact (unique_range_sort H H0 (refl_equal (Srt s)) (refl_equal (Srt s'))).
Qed.
