Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Substitution.
Require Import CCPD.Generation.
Require Import CCPD.UnicityOfSorting.

Theorem coerce_trans : forall e A B C s, e |- A >> B : s -> e |- B >> C : s ->
  e |- A >> C : s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
Admitted.
(*
  induction H2 ; simpl ; intros ; auto with coc.
  apply coerce_conv with A0 A0; auto.
  apply coerce_id ; auto.

  apply coerce_conv with (Prod A0 B) (Prod A' B'); auto with coc.
  apply type_prod with s ; auto with coc.
  apply type_prod with s ; auto with coc.

  apply coerce_prod with s ; auto with coc core.
  apply coerce_conv with e 

  apply coerce_id ; auto.

  

  apply coerce_prod with s ; auto with coc core.
*)