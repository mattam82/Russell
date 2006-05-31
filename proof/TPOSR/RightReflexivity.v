Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Basic.
Require Import Lambda.TPOSR.CtxReduction.
Require Import Lambda.TPOSR.Substitution.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Lemma right_refl : forall e u v T, e |-- u -> v : T -> e |-- v -> v : T.
Admitted.

Corollary conv_refls : forall e u v s, e |-- u ~= v : s -> 
  e |-- u -> u : Srt_l s /\ e |-- v -> v : Srt_l s.
Admitted.

Corollary conv_refl_l :  forall e u v s, e |-- u ~= v : s -> e |-- u -> u : Srt_l s.
Proof.
  intros.
  apply (proj1 (conv_refls H)).
Qed.

Corollary conv_refl_r :  forall e u v s, e |-- u ~= v : s -> e |-- v -> v : Srt_l s.
Proof.
  intros.
  apply (proj2 (conv_refls H)).
Qed.

Lemma tposrp_right_refl : forall e A B T, tposrp e A B T -> e |-- B -> B : T.
Proof.
  induction 1 ; auto with coc.
  apply (right_refl H).
Qed.

Hint Resolve right_refl conv_refl_l conv_refl_r tposrp_right_refl : coc.