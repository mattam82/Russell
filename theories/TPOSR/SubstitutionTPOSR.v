Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.PreCtxCoercion.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.PreSubstitutionTPOSR.
Require Import Lambda.TPOSR.RightReflexivity.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Corollary substitution_tposr_tposr_n : forall g d d' t, g |-- d -> d' : t ->
   forall e u v U, e |-- u -> v : U ->
   forall f n, sub_in_lenv d t n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d u n) -> (lsubst_rec d' v n) : (lsubst_rec d U n).
Proof.
  intros ; eapply substitution_tposr_tposr_n ; eauto with coc.
Qed.

Corollary substitution_tposr_tposr_wf_n : forall g d d' t, g |-- d -> d' : t -> 
   forall e, tposr_wf e -> forall f n, sub_in_lenv d t n e f -> 
   trunc _ n f g -> tposr_wf f.
Proof.
  intros ; eapply substitution_tposr_tposr_wf_n ; eauto with coc.
Qed.

Corollary substitution_tposr_eq_n : forall g d d' t, g |-- d -> d' : t ->
   forall e u v s, e |-- u ~= v : s ->
   forall f n, sub_in_lenv d t n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d u n) ~= (lsubst_rec d' v n) : s.
Proof.
  intros ; eapply substitution_tposr_eq_n ; eauto with coc.
Qed.

Corollary substitution_tposr_coerce_n : forall g d d' t, g |-- d -> d' : t -> 
   forall e u v s, e |-- u >-> v : s ->
   forall f n, sub_in_lenv d t n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d u n) >-> (lsubst_rec d' v n) : s.
Proof.
  intros ; eapply substitution_tposr_coerce_n ; eauto with coc.
Qed.

Corollary substitution_tposr_tposr : forall e t u v U, (t :: e) |-- u -> v : U ->
  forall d d', e |-- d -> d' : t -> e |-- (lsubst d u) -> (lsubst d' v) : (lsubst d U).
Proof.
  intros ; unfold lsubst ; eapply substitution_tposr_tposr_n ; eauto with coc.
Qed.

Corollary substitution_tposr_eq : 
   forall e t u v s, t :: e |-- u ~= v : s ->
   forall d d', e |-- d -> d' : t -> 
   e |-- (lsubst d u) ~= (lsubst d' v) : s.
Proof.
  intros ; unfold lsubst ; eapply substitution_tposr_eq_n ; eauto with coc.
Qed.

Corollary substitution_tposr_coerce : 
   forall e t u v s, t :: e |-- u >-> v : s ->
   forall d d', e |-- d -> d' : t -> 
   e |-- (lsubst d u) >-> (lsubst d' v) : s.
Proof.
  intros ; unfold lsubst ; eapply substitution_tposr_coerce_n ; eauto with coc.
Qed.

Corollary substitution_tposr_tposrp_aux : forall G u v U, G |-- u -+> v : U -> forall t e, G = (t :: e) ->
  forall d d', e |-- d -> d' : t -> 
  e |-- (lsubst d u) -+> (lsubst d' v) : (lsubst d U).
Proof.
  induction 1 ; simpl ; intros; subst ; eauto with coc ecoc.
Qed.

Corollary substitution_tposr_tposrp : forall t e u v U, t :: e |-- u -+> v : U -> 
  forall d d', e |-- d -> d' : t -> 
 e |-- (lsubst d u) -+> (lsubst d' v) : (lsubst d U).
Proof.
  intros.
  eapply substitution_tposr_tposrp_aux  ; eauto with coc.
Qed.

Corollary substitution_sorted_n : 
  forall g d d' t, g |-- d -> d' : t -> 
   forall e u v s, e |-- u -> v : s ->
   forall f n, sub_in_lenv d t n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d u n) -> (lsubst_rec d' v n) : Srt_l s.
Proof.
  intros.
  change (Srt_l s) with (lsubst_rec d (Srt_l s) n).
  eapply substitution_tposr_tposr_n ; eauto with coc.
Qed.

Corollary substitution_sorted : forall e t u v s, (t :: e) |-- u -> v : Srt_l s ->
  forall d d', e |-- d -> d' : t -> e |-- (lsubst d u) -> (lsubst d' v) : Srt_l s.
Proof.
  intros.
  change (Srt_l s) with (lsubst d (Srt_l s)).
  apply substitution_tposr_tposr with t ; auto.
Qed.

Hint Resolve substitution_tposr_tposr substitution_tposr_coerce substitution_tposr_eq substitution_tposr_tposrp : ecoc.
