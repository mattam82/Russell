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

Theorem coerce_rc_depth_sym : forall e A B s n, e |-- A >-> B : s [n] ->
  e |-- B >-> A : s [n].
Proof.
  induction 1 ; simpl ; intros ; auto with coc.

  apply coerce_rc_depth_prod with s ; eauto with coc ecoc.
  apply coerce_rc_depth_conv_env with (A' :: e) ; auto with coc.
  apply coerce_rc_depth_env_hd with s n ; auto.

  apply coerce_rc_depth_sum with s s' ; eauto with coc ecoc.
  apply coerce_rc_depth_conv_env with (A :: e) ; auto with coc.
  apply coerce_rc_depth_env_hd with s n ; auto.

  apply coerce_rc_depth_conv_r with B ; eauto with coc ecoc.
  apply coerce_rc_depth_conv_l with B ; eauto with coc ecoc.
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


