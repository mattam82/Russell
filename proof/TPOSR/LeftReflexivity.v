Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Basic.
Require Import Lambda.TPOSR.CtxReduction.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Lemma left_refl : forall e u v T, e |-- u -> v : T -> e |-- u -> u : T.
Admitted.

Corollary tposrp_left_refl : forall e A B T, tposrp e A B T -> e |-- A -> A : T.
Proof.
  induction 1 ; auto with coc.
  apply (left_refl H).
Qed.


Hint Resolve left_refl tposrp_left_refl : coc.