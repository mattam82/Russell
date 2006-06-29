Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.MyList.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Basic.
Require Import Lambda.TPOSR.Thinning.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.CtxConversion.
Require Import Lambda.TPOSR.RightReflexivity.

Require Import Lambda.Meta.TPOSR_Russell.

Set Implicit Arguments.

Definition unique_sort := tposr_unique_sort.
Definition eq_unique_sort := tposr_eq_unique_sort.
Definition coerce_unique_sort := tposr_coerce_unique_sort.

Hint Unfold unique_sort eq_unique_sort : coc.

Hint Resolve unique_sort eq_unique_sort : coc.

Lemma tposrp_unique_sort : forall G A s t, 
  tposr_term G A (Srt_l s) -> tposr_term G A (Srt_l t) -> s = t.
Proof.
  unfold tposr_term ; intros ; destruct_exists.
  eauto with coc.
Qed.

Hint Resolve tposrp_unique_sort : coc.
