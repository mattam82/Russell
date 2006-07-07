Require Import Lambda.Tactics.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.TypesNoDerivs.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.Thinning.
Require Import Lambda.TPOSR.CtxReduction.
Require Import Lambda.TPOSR.CtxExpansion.
Require Import Lambda.TPOSR.Substitution.

Require Import Coq.Arith.Lt.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Lemma sub_red_env : forall g d d' T, g |-- d -> d' : T -> g |-- d' -> d' : T ->
  forall n e f, sub_in_lenv d T n e f -> trunc lterm n f g ->
  exists f', (sub_in_lenv d' T n e f' /\ trunc lterm n f' g).
Proof.
  intros.
  induction H1 ; simpl.
  inversion H2 ; subst.
  exists g.
  intuition.
  inversion H2.
  subst.

  inversion H2.
  subst.
  destruct (IHsub_in_lenv H7).
  exists (lsubst_rec d' u n :: x).
  destruct H3.
  clear IHsub_in_lenv ; intuition.
Qed.

Lemma ind_substitution_tposr : 
   (forall e t u U, e |-- t -> u : U ->
   forall g d d' T, g |-- d -> d' : T -> g |-- d' -> d' : T ->
   forall f n, sub_in_lenv d T n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d t n) -> (lsubst_rec d' u n) : (lsubst_rec d U n)) /\
   (forall e, tposr_wf e ->
   forall g d d' T, g |-- d -> d' : T -> g |-- d' -> d' : T ->
   forall n f, sub_in_lenv d T n e f -> trunc _ n f g -> 
   tposr_wf f) /\
   (forall e t u s, e |-- t ~= u : s ->
   forall g d d' T, g |-- d -> d' : T -> g |-- d' -> d' : T ->
   forall f n, sub_in_lenv d T n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d t n) ~= (lsubst_rec d' u n) : s /\
   f |-- (lsubst_rec d' t n) ~= (lsubst_rec d u n) : s) /\
   (forall e t u s, e |-- t >-> u : s ->
   forall g d d' T, g |-- d -> d' : T -> g |-- d' -> d' : T ->
   forall f n, sub_in_lenv d T n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d t n) >-> (lsubst_rec d' u n) : s /\
   f |-- (lsubst_rec d' t n) >-> (lsubst_rec d u n) : s).
Proof.
apply ind_tposr_wf_eq_coerce with
   (P:=fun e t u U => fun H : e |-- t -> u : U =>
   forall g d d' T, g |-- d -> d' : T -> g |-- d' -> d' : T ->
   forall f n, sub_in_lenv d T n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d t n) -> (lsubst_rec d' u n) : (lsubst_rec d U n))
   (P0:= fun e => fun H : tposr_wf e =>
   forall g d d' T, g |-- d -> d' : T -> g |-- d' -> d' : T ->
   forall n f, sub_in_lenv d T n e f -> trunc _ n f g -> 
   tposr_wf f)
   (P1 := fun e t u s => fun H : e |-- t ~= u : s =>
   forall g d d' T, g |-- d -> d' : T -> g |-- d' -> d' : T ->
   forall f n, sub_in_lenv d T n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d t n) ~= (lsubst_rec d' u n) : s /\
   f |-- (lsubst_rec d' t n) ~= (lsubst_rec d u n) : s)
   (P2 := fun e t u s => fun H : e |-- t >-> u : s =>
   forall g d d' T, g |-- d -> d' : T -> g |-- d' -> d' : T ->
   forall f n, sub_in_lenv d T n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d t n) >-> (lsubst_rec d' u n) : s /\
   f |-- (lsubst_rec d' t n) >-> (lsubst_rec d u n) : s);
   simpl in |- *;
   intros; auto with coc core arith datatypes.

elim (lt_eq_lt_dec n0 n); [ intro Hlt_eq | intro Hlt ].
elim i.
elim Hlt_eq; clear Hlt_eq.
case n; [ intro Hlt | intros n1 Hlt ]; intros.
inversion_clear Hlt.

simpl in |- *.
rewrite H4.
rewrite simpl_lsubst; auto with coc core arith datatypes.
apply tposr_var; auto with coc core arith datatypes.
apply (H _ _ _ _ H0 H1 _ _ H2) ; auto.
exists x; auto with coc core arith datatypes.
apply nth_sub_sup with d T0 n0 e; auto with coc core arith datatypes.

intro Heq; intros.
rewrite H4.
elim Heq.
rewrite simpl_lsubst; auto with coc core arith datatypes.
replace x with T0.
apply thinning_n with g; auto with coc core arith datatypes.
subst.
apply (H _ _ _ _ H0 H1 _ _ H2) ; auto.

apply fun_item with e n; auto with coc core arith datatypes.
apply nth_sub_eq with d f; auto with coc core arith datatypes.
elim Heq; auto with coc core arith datatypes.

apply tposr_var; auto with coc core arith datatypes.
apply (H _ _ _ _ H0 H1 _ _ H2) ; auto.
apply nth_sub_inf with T0 e; auto with coc core arith datatypes.

apply tposr_set ; eauto with coc.

apply tposr_prop ; eauto with coc.

apply tposr_prod with s1 ; eauto with coc ecoc core arith datatypes.

apply tposr_abs with s1 (lsubst_rec d' B' (S n)) s2 ; eauto with coc core arith datatypes.

rewrite distr_lsubst ; auto with coc.
apply tposr_app with (lsubst_rec d A n) (lsubst_rec d A' n) s1 s2; eauto with coc core arith datatypes.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H0 _ _ _ _ H3 H4 _ _ H7 H8) ; auto with coc.

rewrite distr_lsubst ; auto with coc.
rewrite distr_lsubst ; auto with coc.
apply tposr_beta with (lsubst_rec d' A' n) s1  (lsubst_rec d' B' (S n)) s2; eauto with coc core arith datatypes.

apply tposr_conv with (lsubst_rec d A n) s; eauto with coc.
apply substitution_coerce_n with g T e ; eauto with coc.

apply tposr_subset ; eauto with coc.

apply tposr_sum with s1 s2; eauto with coc core arith datatypes.

apply tposr_pair with s1 s2 s3 ; eauto with coc.
rewrite <- distr_lsubst ; eauto with coc.

pose (H _ _ _ _ H3 H4 _ _ H5 H6).
destruct (H0 _ _ _ _ H3 H4 _ _ H5 H6) ; auto with coc.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H1 _ _ _ _ H3 H4 _ _ H9 H10) ; auto with coc.
apply tposr_pi1 with s1 s2 s3 ; eauto with coc.

apply tposr_pi1_red with (lsubst_rec d' A' n) s1 (lsubst_rec d' B' (S n))  s2 s3 (lsubst_rec d' v' n); eauto with coc.
rewrite <- distr_lsubst.
eauto with coc.

rewrite distr_lsubst.
simpl.
pose (H _ _ _ _ H3 H4 _ _ H5 H6).
destruct (H0 _ _ _ _ H3 H4 _ _ H5 H6) ; auto with coc.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H1 _ _ _ _ H3 H4 _ _ H9 H10) ; auto with coc.
apply tposr_pi2 with s1 s2 s3 ; eauto with coc.

rewrite distr_lsubst.
simpl.
apply tposr_pi2_red with (lsubst_rec d' A' n) s1 (lsubst_rec d' B' (S n))  s2 s3 (lsubst_rec d' u' n); eauto with coc.
rewrite <- distr_lsubst ; eauto with coc.

inversion H1.
inversion H2 ; subst.
apply (wf_tposr t).
inversion H3.
apply wf_cons with (lsubst_rec d' A' n0) s ; apply (H _ _ _ _ H0 H1 _ _ H8 H9).

split ; eauto with coc ecoc.
apply tposr_eq_trans with (lsubst_rec d X n) ; eauto with coc.
apply tposr_eq_sym.
apply tposr_eq_tposr.
eapply H ; eauto with coc.
eapply H ; eauto with coc.
apply substitution_eq_n with g T e ; eauto with coc.

destruct (H _ _ _ _ H0 H1 _ _ H2 H3).
intuition.

destruct (H _ _ _ _ H1 H2 _ _ H3 H4).
destruct (H0 _ _ _ _ H1 H2 _ _ H3 H4).
destruct (H _ _ _ _ (refl_l H1) (refl_l H1) _ _ H3 H4).
destruct (H0 _ _ _ _ (refl_l H1) (refl_l H1) _ _ H3 H4).

split.
apply tposr_eq_trans with (lsubst_rec d X n) ; eauto with coc.
apply tposr_eq_trans with (lsubst_rec d X n) ; eauto with coc.

destruct (H _ _ _ _ H0 H1 _ _ H2 H3).
auto with coc.

destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
assert(sub_in_lenv d T (S n) (A' :: e) (lsubst_rec d A' n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A' n :: f) g).
apply trunc_S ; auto with coc.
destruct (H2 _ _ _ _ H3 H4 _ _ H9 H10) ; auto with coc.
split ; apply tposr_coerce_prod with s ; eauto with coc.
destruct (sub_red_env H3 H4 H5 H6).
destruct_exists.
pose (H0 _ _ _ _ H4 H4 _ _ H13 H14).
apply tposr_exp_env with x ; auto with coc.

Focus 5.
destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
assert(sub_in_lenv d T (S n) (U :: e) (lsubst_rec d U n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d U n :: f) g).
apply trunc_S ; auto with coc.
pose (H0 _ _ _ _(refl_l H3) (refl_l H3) _ _ H5 H6).

split ; apply tposr_coerce_sub_l ; auto with coc ecoc.
apply tposr_coerce_conv.
apply tposr_eq_tposr ; auto with coc.
eauto with coc ecoc.

Admitted.



(*

pose

apply 
coerce_red_env with (lsubst_rec d A' n :: f) ; auto with coc.
apply red_env_hd with s.
eapply H0 ; eauto with coc.


split.
destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
apply tposr_coerce_sub_l ; eauto with coc.
Focus 2.
destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
assert(sub_in_lenv d T (S n) (U :: e) (lsubst_rec d U n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d U n :: f) g).
apply trunc_S ; auto with coc.
pose (H2 _ _ _ _ H3 H4 _ _ H9 H10).
apply tposr_coerce_sub_l ; eauto with coc.
Focus 2.
split ; apply tposr_coerce_prod with s ; auto with coc.

  


apply substitution_sorted_n with g T e ; auto with coc.


apply tposr_coerce_sum with s s' ; eauto with coc.

apply tposr_coerce_sub_l ; eauto with coc.

apply tposr_coerce_sub_r ; eauto with coc.

eauto with coc.

apply tposr_coerce_trans with (lsubst_rec d B n) ; eauto with coc.
Qed.
*)

Corollary substitution_tposr_tposr_n : forall g d d' t, g |-- d -> d' : t -> g |-- d' -> d' : t ->
   forall e u v U, e |-- u -> v : U ->
   forall f n, sub_in_lenv d t n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d u n) -> (lsubst_rec d' v n) : (lsubst_rec d U n).
Proof.
  intros.
  eapply (proj1 (ind_substitution_tposr)) ; eauto with coc.
Qed.

Corollary substitution_tposr_tposr_wf_n : forall g d d' t, g |-- d -> d' : t -> g |-- d' -> d' : t ->
   forall e, tposr_wf e -> forall f n, sub_in_lenv d t n e f -> 
   trunc _ n f g -> tposr_wf f.
Proof.
  intros.
  apply (proj1 (proj2 (ind_substitution_tposr))) with e g d d' t n ; eauto with coc.
Qed.

Corollary substitution_tposr_eq_n : forall g d d' t, g |-- d -> d' : t -> g |-- d' -> d' : t ->
   forall e u v s, e |-- u ~= v : s ->
   forall f n, sub_in_lenv d t n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d u n) ~= (lsubst_rec d' v n) : s.
Proof.
  intros.
  pose (proj1 (proj2 (proj2 (ind_substitution_tposr)))) ; eauto with coc.
  destruct (a _ _ _ _ H1 _ _ _ _ H H0 _ _ H2 H3) ; auto.
Qed.

Corollary substitution_tposr_coerce_n : forall g d d' t, g |-- d -> d' : t -> g |-- d' -> d' : t ->
   forall e u v s, e |-- u >-> v : s ->
   forall f n, sub_in_lenv d t n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d u n) >-> (lsubst_rec d' v n) : s.
Proof.
  intros.
  pose (proj2 (proj2 (proj2 (ind_substitution_tposr)))) ; eauto with coc.
  destruct (a _ _ _ _ H1 _ _ _ _ H H0 _ _ H2 H3) ; auto.
Qed.

Corollary substitution_tposr_tposr : forall e t u v U, (t :: e) |-- u -> v : U ->
  forall d d', e |-- d -> d' : t -> e |-- d' -> d' : t -> 
  e |-- (lsubst d u) -> (lsubst d' v) : (lsubst d U).
Proof.
  intros ; unfold lsubst ; eapply substitution_tposr_tposr_n ; eauto with coc.
Qed.

Corollary substitution_tposr_eq : 
   forall e t u v s, t :: e |-- u ~= v : s ->
   forall d d', e |-- d -> d' : t -> e |-- d' -> d' : t ->
   e |-- (lsubst d u) ~= (lsubst d' v) : s.
Proof.
  intros ; unfold lsubst ; eapply substitution_tposr_eq_n ; eauto with coc.
Qed.

Corollary substitution_tposr_coerce : 
   forall e t u v s, t :: e |-- u >-> v : s ->
   forall d d', e |-- d -> d' : t -> e |-- d' -> d' : t ->
   e |-- (lsubst d u) >-> (lsubst d' v) : s.
Proof.
  intros ; unfold lsubst ; eapply substitution_tposr_coerce_n ; eauto with coc.
Qed.

Corollary substitution_tposr_tposrp_aux : forall G u v U, G |-- u -+> v : U -> forall t e, G = (t :: e) ->
  forall d d', e |-- d -> d' : t -> e |-- d' -> d' : t ->
  e |-- (lsubst d u) -+> (lsubst d' v) : (lsubst d U).
Proof.
  induction 1 ; simpl ; intros; subst ; eauto with coc ecoc.
  apply tposrp_tposr.
  apply substitution_tposr_tposr with t ; auto.
Qed.

Corollary substitution_tposr_tposrp : forall t e u v U, t :: e |-- u -+> v : U -> 
  forall d d', e |-- d -> d' : t -> e |-- d' -> d' : t ->
 e |-- (lsubst d u) -+> (lsubst d' v) : (lsubst d U).
Proof.
  intros.
  eapply substitution_tposr_tposrp_aux  ; eauto with coc.
Qed.

Corollary substitution_sorted_n : 
  forall g d d' t, g |-- d -> d' : t -> g |-- d' -> d' : t ->
   forall e u v s, e |-- u -> v : s ->
   forall f n, sub_in_lenv d t n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d u n) -> (lsubst_rec d' v n) : Srt_l s.
Proof.
  intros.
  change (Srt_l s) with (lsubst_rec d (Srt_l s) n).
  eapply substitution_tposr_tposr_n ; eauto with coc.
Qed.

Corollary substitution_sorted : forall e t u v s, (t :: e) |-- u -> v : Srt_l s ->
  forall d d', e |-- d -> d' : t -> e |-- d' -> d' : t -> e |-- (lsubst d u) -> (lsubst d' v) : Srt_l s.
Proof.
  intros.
  change (Srt_l s) with (lsubst d (Srt_l s)).
  apply substitution_tposr_tposr with t ; auto.
Qed.

Hint Resolve substitution_tposr_tposr substitution_tposr_coerce substitution_tposr_eq substitution_tposr_tposrp : ecoc.
