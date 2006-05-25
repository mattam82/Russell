Require Import TPOSR.Terms.
Require Import TPOSR.Reduction.
Require Import TPOSR.Conv.
Require Import TPOSR.LiftSubst.
Require Import TPOSR.Env.
Require Import TPOSR.Types.
Require Import TPOSR.Basic.
Require Import TPOSR.CtxReduction.
Require Import TPOSR.Substitution.

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

Hint Resolve right_refl conv_refls : coc.