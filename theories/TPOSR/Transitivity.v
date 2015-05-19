Require Import Lambda.Utils.
Require Import Lambda.Tactics.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Basic.
Require Import Lambda.TPOSR.Thinning.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.CtxCoercion.
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.ChurchRosser.
Require Import Lambda.TPOSR.CoerceDepth.
Require Import Lambda.TPOSR.CoerceNoTrans.
Require Import Lambda.TPOSR.TransitivitySet.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.


Theorem coerces_trans : forall e A B C s, e |-- A >>> B : s -> e |-- B >>> C : s ->
  e |-- A >>> C : s.
Proof.
  intros.
  set (x := depth H).
  set (y := depth H0).
  set (sum := x + y).
  apply (@coerce_trans_aux sum e A B s H C H0).
  unfold sum, x, y.
  reflexivity.
Qed.

Require Import Lambda.TPOSR.CoerceDepth.

Theorem coerce_rc_depth_trans : forall e A B C s n1 n2, e |-- A >-> B : s [n1] -> e |-- B >-> C : s [n2]->
  exists m, e |-- A >-> C : s [m].
Proof.
  intros.
  destruct (coerce_rc_depth_coerces H).
  destruct (coerce_rc_depth_coerces H0).
  pose (coerces_trans x x0).
  pose (coerces_coerce_rc_depth c).
  exists (depth c) ; auto.
Qed.

Theorem coerce_rc_depth_sym : forall e A B s n, e |-- A >-> B : s [n] ->
  e |-- B >-> A : s [n].
Proof.
  intros.
  destruct (coerce_rc_depth_coerces H).
  destruct (coerces_sym x).
  pose (coerces_coerce_rc_depth x0).
  rewrite <- H0.
  rewrite <- e0 ; auto.
Qed.

Theorem coerce_coerce_rc_depth : forall e A B s, e |-- A >-> B : s -> exists n, e |-- A >-> B : s [n].
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  
  exists 1 ; auto with coc.
  apply coerce_rc_depth_conv_l with B ; eauto with coc ecoc.

  destruct_exists.
  exists (S (max x0 x)).
  apply coerce_rc_depth_prod with s ; eauto with coc ecoc.

  destruct_exists.
  exists (S (max x0 x)).
  apply coerce_rc_depth_sum with s s' ; eauto with coc ecoc.

  destruct_exists.
  exists (S x).
  apply coerce_rc_depth_sub_l  ; eauto with coc ecoc.

  destruct_exists.
  exists (S x).
  apply coerce_rc_depth_sub_r ; eauto with coc ecoc.

  destruct_exists.
  exists x.
  apply coerce_rc_depth_sym  ; eauto with coc ecoc.

  destruct_exists.
  apply coerce_rc_depth_trans with B x0 x ; auto.
Qed.


