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
Require Import Lambda.TPOSR.CtxCoercion.
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

Lemma wf_coerce : forall e, tposr_wf e -> coerce_in_env_full e e.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  apply coerce_env_in_env.
  apply coerce_env_hd with s ; eauto with coc.
Qed.  

Lemma coerce_env_full_cons_coerce : forall G D, coerce_in_env_full G D -> 
  forall T U s, G |-- T >-> U : s -> G |-- T -> T : s -> G |-- U -> U : s ->
  coerce_in_env_full (T :: G) (U :: D).
Proof.
  induction 1 ; simpl ; intros.

  apply coerce_env_trans with (U :: f) ; eauto with coc.
  apply coerce_env_full_cons ; auto with coc.
  apply wf_cons with s ; eauto with coc.
  apply coerce_env_full with e ; auto.

  apply coerce_env_trans with (T :: f).
  apply coerce_env_in_env ; eauto with coc.

  apply coerce_env_in_env ; eauto with coc.
  apply coerce_env_hd with s ; eauto with coc.
  apply coerce_coerce_env with e ; eauto with coc.
  apply tposr_coerce_env with e ; eauto with coc.
  apply tposr_coerce_env with e ; eauto with coc.
  
  apply coerce_env_in_env ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
Qed.

Lemma ind_substitution_tposr : 
   (forall e t u U, e |-- t -> u : U ->
   forall g d d' T, g |-- d -> d' : T -> g |-- d' -> d' : T ->
   forall f n, sub_in_lenv d T n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d t n) -> (lsubst_rec d' u n) : (lsubst_rec d U n) /\
   exists f', sub_in_lenv d' T n e f' /\ trunc _ n f' g /\
   tposr_wf f' /\ coerce_in_env_full f f') /\
   (forall e, tposr_wf e ->
   forall g d d' T, g |-- d -> d' : T -> g |-- d' -> d' : T ->
   forall n f, sub_in_lenv d T n e f -> trunc _ n f g -> 
   tposr_wf f /\
   exists f', sub_in_lenv d' T n e f' /\ trunc _ n f' g /\
   tposr_wf f' /\ coerce_in_env_full f f'
   ) /\
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
   f |-- (lsubst_rec d t n) -> (lsubst_rec d' u n) : (lsubst_rec d U n) /\
   exists f', sub_in_lenv d' T n e f' /\ trunc _ n f' g /\
   tposr_wf f' /\ coerce_in_env_full f f')
   (P0:= fun e => fun H : tposr_wf e =>
   forall g d d' T, g |-- d -> d' : T -> g |-- d' -> d' : T ->
   forall n f, sub_in_lenv d T n e f -> trunc _ n f g -> 
   tposr_wf f /\
   exists f', sub_in_lenv d' T n e f' /\ trunc _ n f' g /\
   tposr_wf f' /\ coerce_in_env_full f f')
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

split.
elim (lt_eq_lt_dec n0 n); [ intro Hlt_eq | intro Hlt ].
elim i.
elim Hlt_eq; clear Hlt_eq.
case n; [ intro Hlt | intros n1 Hlt ]; intros.
inversion_clear Hlt.

simpl in |- *.
rewrite H4.
rewrite simpl_lsubst; auto with coc core arith datatypes.
apply tposr_var; auto with coc core arith datatypes.
destruct (H _ _ _ _ H0 H1 _ _ H2) ; auto.
exists x; auto with coc core arith datatypes.
apply nth_sub_sup with d T0 n0 e; auto with coc core arith datatypes.

intro Heq; intros.
rewrite H4.
elim Heq.
rewrite simpl_lsubst; auto with coc core arith datatypes.
replace x with T0.
apply thinning_n with g; auto with coc core arith datatypes.
subst.
destruct (H _ _ _ _ H0 H1 _ _ H2) ; auto.

apply fun_item with e n; auto with coc core arith datatypes.
apply nth_sub_eq with d f; auto with coc core arith datatypes.
elim Heq; auto with coc core arith datatypes.

apply tposr_var; auto with coc core arith datatypes.
destruct (H _ _ _ _ H0 H1 _ _ H2) ; auto.
apply nth_sub_inf with T0 e; auto with coc core arith datatypes.

destruct (H _ _ _ _ H0 H1 _ _ H2) ; auto.
destruct (H _ _ _ _ H0 H1 _ _ H2) ; auto.
split ; [apply tposr_set|idtac] ; eauto with coc.

destruct (H _ _ _ _ H0 H1 _ _ H2) ; auto.
split ; [apply tposr_prop|idtac] ; eauto with coc.

destruct (H _ _ _ _ H1 H2 _ _ H3 H4).
split ; auto.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H0 _ _ _ _ H1 H2 _ _ H7 H8) ; auto.
apply tposr_prod with s1 ; eauto with coc ecoc core arith datatypes.

destruct (H _ _ _ _ H2 H3 _ _ H4 H5).
split ; auto.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H1 _ _ _ _ H2 H3 _ _ H8 H9) ; auto.
destruct (H0 _ _ _ _ H2 H3 _ _ H8 H9) ; auto.
apply tposr_abs with s1 (lsubst_rec d' B' (S n)) s2 ; eauto with coc core arith datatypes.

destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
split ; auto.
rewrite distr_lsubst ; auto with coc.
destruct (H2 _ _ _ _ H3 H4 _ _ H5 H6).
destruct (H1 _ _ _ _ H3 H4 _ _ H5 H6).
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H0 _ _ _ _ H3 H4 _ _ H13 H14).
destruct (H _ _ _ _ (refl_l H3) (refl_l H3) _ _ H5 H6).
apply tposr_app with (lsubst_rec d A n) (lsubst_rec d A' n) s1 s2; eauto with coc core arith datatypes.

rewrite distr_lsubst ; auto with coc.
rewrite distr_lsubst ; auto with coc.
destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
split ; auto.
destruct (H2 _ _ _ _ H3 H4 _ _ H5 H6).
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H0 _ _ _ _ H3 H4 _ _ H11 H12).
destruct (H1 _ _ _ _ H3 H4 _ _ H11 H12).
apply tposr_beta with (lsubst_rec d' A' n) s1  (lsubst_rec d' B' (S n)) s2; eauto with coc core arith datatypes.

destruct (H _ _ _ _ H1 H2 _ _ H3 H4).
split ; auto.
apply tposr_conv with (lsubst_rec d A n) s; eauto with coc.
apply substitution_coerce_n with g T e ; eauto with coc.

destruct (H _ _ _ _ H1 H2 _ _ H3 H4).
split ; eauto with coc.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H0 _ _ _ _ H1 H2 _ _ H7 H8).
apply tposr_subset ; eauto with coc.

destruct (H _ _ _ _ H1 H2 _ _ H3 H4).
split ; auto.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H0 _ _ _ _ H1 H2 _ _ H7 H8) ; auto with coc.
apply tposr_sum with s1 s2; eauto with coc core arith datatypes.

destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
split ; auto.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H2 _ _ _ _ H3 H4 _ _ H5 H6).
destruct (H1 _ _ _ _ H3 H4 _ _ H5 H6).
destruct (H0 _ _ _ _ H3 H4 _ _ H9 H10).
apply tposr_pair with s1 s2 s3 ; eauto with coc.
rewrite <- distr_lsubst ; eauto with coc.

destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
split ; auto.
destruct (H0 _ _ _ _ H3 H4 _ _ H5 H6) ; auto with coc.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H1 _ _ _ _ H3 H4 _ _ H11 H12) ; auto with coc.
destruct (H2 _ _ _ _ H3 H4 _ _ H5 H6) ; auto with coc.
apply tposr_pi1 with s1 s2 s3 ; eauto with coc.

destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
split ; auto.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H1 _ _ _ _ H3 H4 _ _ H9 H10) ; auto with coc.
destruct (H2 _ _ _ _ H3 H4 _ _ H5 H6) ; auto with coc.
destruct (H0 _ _ _ _ H3 H4 _ _ H5 H6) ; auto with coc.
apply tposr_pi1_red with s1 s2 s3 (lsubst_rec d' A'' n) (lsubst_rec d' B'' (S n)) (lsubst_rec d' v' n); eauto with coc.
destruct (H0 _ _ _ _ (refl_l H3) (refl_l H3) _ _ H5 H6) ; auto with coc.
destruct (H1 _ _ _ _ (refl_l H3) (refl_l H3) _ _ H9 H10) ; auto with coc.

rewrite distr_lsubst.
simpl.
destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
split ; auto.
destruct (H0 _ _ _ _ H3 H4 _ _ H5 H6) ; auto with coc.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H1 _ _ _ _ H3 H4 _ _ H11 H12) ; auto with coc.
destruct (H2 _ _ _ _ H3 H4 _ _ H5 H6) ; auto with coc.
apply tposr_pi2 with s1 s2 s3 ; eauto with coc.

rewrite distr_lsubst.
simpl.
destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
split ; auto.

assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H1 _ _ _ _ H3 H4 _ _ H9 H10) ; auto with coc.
destruct (H2 _ _ _ _ H3 H4 _ _ H5 H6) ; auto with coc.
destruct (H0 _ _ _ _ H3 H4 _ _ H5 H6) ; auto with coc.
apply tposr_pi2_red with s1 s2 s3 (lsubst_rec d' A'' n) (lsubst_rec d' B'' (S n)) (lsubst_rec d' u' n); eauto with coc.
destruct (H0 _ _ _ _ (refl_l H3) (refl_l H3) _ _ H5 H6) ; auto with coc.
destruct (H1 _ _ _ _ (refl_l H3) (refl_l H3) _ _ H9 H10) ; auto with coc.

inversion H1.
inversion H2 ; subst.
assert(tposr_wf f) by apply (wf_tposr t).
split ; auto.
exists f.
split ; intuition.
apply (wf_coerce H4).

inversion H3.
destruct (H _ _ _ _ H0 H1 _ _ H8 H9).
split ; auto.
destruct (H _ _ _ _ (refl_l H0) (refl_l H0) _ _ H8 H9).
subst.
apply wf_cons with s ; auto.
destruct H11 ; destruct_exists.
exists (lsubst_rec d' A n0 :: x0).
subst.
destruct (H _ _ _ _ H1 H1 _ _ H11 H12).
intuition ; auto with coc.
apply wf_cons with s ; auto with coc.
apply coerce_env_full_cons_coerce with s ; eauto with coc.
apply coerce_env_full with x0 ; eauto with coc ecoc.

destruct (H _ _ _ _ H1 H2 _ _ H3 H4).
destruct (H0 _ _ _ _ H1 H2 _ _ H3 H4).
destruct (H _ _ _ _ (refl_l H1) (refl_l H1) _ _ H3 H4).
destruct (H0 _ _ _ _ (refl_l H1) (refl_l H1) _ _ H3 H4).

split.
apply tposr_eq_trans with (lsubst_rec d X n) ; eauto with coc.
apply tposr_eq_trans with (lsubst_rec d X n) ; eauto with coc.

destruct (H _ _ _ _ H0 H1 _ _ H2 H3) ; auto with coc.

destruct (H _ _ _ _ H1 H2 _ _ H3 H4).
destruct (H0 _ _ _ _ H1 H2 _ _ H3 H4).
destruct (H _ _ _ _ (refl_l H1) (refl_l H1) _ _ H3 H4).
destruct (H0 _ _ _ _ (refl_l H1) (refl_l H1) _ _ H3 H4).

split ; apply tposr_eq_trans with (lsubst_rec d X n) ; eauto with coc.

destruct (H _ _ _ _ H0 H1 _ _ H2 H3) ; auto with coc.

destruct (H _ _ _ _ H5 H6 _ _ H7 H8) ; auto with coc.
assert(sub_in_lenv d T (S n) (A' :: e) (lsubst_rec d A' n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A' n :: f) g).
apply trunc_S ; auto with coc.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H2 _ _ _ _ H5 H6 _ _ H11 H12) ; auto with coc.
destruct (H0 _ _ _ _ H5 H6 _ _ H7 H8) ; destruct_exists.
assert(sub_in_lenv d' T (S n) (A' :: e) (lsubst_rec d' A' n :: x)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d' A' n :: x) g).
apply trunc_S ; auto with coc.
assert(sub_in_lenv d' T (S n) (A :: e) (lsubst_rec d' A n :: x)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d' A n :: x) g).
apply trunc_S ; auto with coc.

destruct (H0 _ _ _ _ H6 H6 _ _ H18 H19).
clear H27.
destruct (H1 _ _ _ _ (refl_l H5) (refl_l H5) _ _ H7 H8).
clear H28.
destruct (H3 _ _ _ _ (refl_l H5) (refl_l H5) _ _ H13 H14).
destruct_exists.
destruct (H3 _ _ _ _ H6 H6 _ _ H24 H25).
clear H34.
destruct (H4 _ _ _ _ H6 H6 _ _ H22 H23).
clear H35.
destruct (H0 _ _ _ _ (refl_l H5) (refl_l H5) _ _ H7 H8).
clear H36.
destruct (H1 _ _ _ _ H5 H6 _ _ H7 H8) ; auto.
destruct_exists.
destruct (H1 _ _ _ _ H6 H6 _ _ H37 H38) ; auto.
clear H42.

split.
apply tposr_coerce_prod with s ; auto with coc.
apply coerce_env_full with x ; auto with coc.

apply coerce_red_env with (lsubst_rec d A' n :: f) ; auto with coc.
apply red_env_hd with s ; auto.
apply coerce_env_full with x ; auto with coc.

apply coerce_env_full with (lsubst_rec d' A' n :: x) ; auto with coc. 
apply coerce_env_full_cons ; auto with coc.
apply wf_cons with s ; auto with coc.

apply tposr_coerce_prod with s ; auto with coc.
apply coerce_env_full with x1 ; auto with coc.

apply coerce_env_full with (lsubst_rec d' A n :: x) ; auto with coc. 
apply coerce_env_full_cons ; auto with coc.
apply wf_cons with s ; auto with coc.
apply coerce_env_full with f ; auto with coc.
apply coerce_env_full with x1 ; auto with coc.
destruct (H4 _ _ _ _ (refl_l H5) (refl_l H5) _ _ H11 H12).
assumption.

destruct (H _ _ _ _ H5 H6 _ _ H7 H8) ; auto with coc.
assert(sub_in_lenv d T (S n) (A' :: e) (lsubst_rec d A' n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A' n :: f) g).
apply trunc_S ; auto with coc.
assert(sub_in_lenv d T (S n) (A :: e) (lsubst_rec d A n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d A n :: f) g).
apply trunc_S ; auto with coc.
destruct (H2 _ _ _ _ H5 H6 _ _ H13 H14) ; auto with coc.
destruct (H0 _ _ _ _ H5 H6 _ _ H7 H8) ; destruct_exists.
assert(sub_in_lenv d' T (S n) (A' :: e) (lsubst_rec d' A' n :: x)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d' A' n :: x) g).
apply trunc_S ; auto with coc.
assert(sub_in_lenv d' T (S n) (A :: e) (lsubst_rec d' A n :: x)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d' A n :: x) g).
apply trunc_S ; auto with coc.

destruct (H0 _ _ _ _ H6 H6 _ _ H18 H19).
clear H27.
destruct (H1 _ _ _ _ (refl_l H5) (refl_l H5) _ _ H7 H8).
clear H28.
destruct (H3 _ _ _ _ (refl_l H5) (refl_l H5) _ _ H13 H14).
destruct_exists.
destruct (H3 _ _ _ _ H6 H6 _ _ H24 H25).
clear H34.
destruct (H4 _ _ _ _ H6 H6 _ _ H22 H23).
clear H35.
destruct (H0 _ _ _ _ (refl_l H5) (refl_l H5) _ _ H7 H8).
clear H36.
destruct (H1 _ _ _ _ H5 H6 _ _ H7 H8) ; auto.
destruct_exists.
destruct (H1 _ _ _ _ H6 H6 _ _ H37 H38) ; auto.
clear H42.

split.
apply tposr_coerce_sum with s s' ; auto with coc.
apply coerce_env_full with x ; auto with coc.

apply coerce_env_full with (lsubst_rec d' A' n :: x) ; auto with coc. 
apply coerce_env_full_cons ; auto with coc.
apply wf_cons with s ; auto with coc.

apply tposr_coerce_sum with s s' ; auto with coc.
apply coerce_env_full with x1 ; auto with coc.

apply coerce_red_env with (lsubst_rec d A n :: f) ; auto with coc.
apply red_env_hd with s ; auto.
apply coerce_env_full with x1 ; auto with coc.

apply coerce_env_full with (lsubst_rec d' A n :: x) ; auto with coc. 
apply coerce_env_full_cons ; auto with coc.
apply wf_cons with s ; auto with coc.
apply coerce_env_full with f ; auto with coc.
apply coerce_env_full with x1 ; auto with coc.

destruct (H4 _ _ _ _ (refl_l H5) (refl_l H5) _ _ H11 H12).
assumption.

destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
assert(sub_in_lenv d T (S n) (U :: e) (lsubst_rec d U n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d U n :: f) g).
apply trunc_S ; auto with coc.
destruct (H2 _ _ _ _ H3 H4 _ _ H9 H10) ; auto with coc.
destruct (H0 _ _ _ _ H3 H4 _ _ H5 H6).
destruct_exists.
destruct (H0 _ _ _ _ H4 H4 _ _ H14 H15).
destruct (H1 _ _ _ _ (refl_l H3) (refl_l H3) _ _ H5 H6) ; auto.
destruct (H0 _ _ _ _ (refl_l H3) (refl_l H3) _ _ H5 H6) ; auto.
destruct (H1 _ _ _ _  H3 H4 _ _ H5 H6) ; auto.
destruct (H1 _ _ _ _  H4 H4 _ _ H14 H15) ; auto.

split ; 
apply tposr_coerce_sub_l ; eauto with coc.
apply coerce_env_full with x ; auto with coc.
apply coerce_env_full with x ; auto with coc.

change (Srt_l prop) with (lsubst_rec d' (Srt_l prop) (S n)).
assert(sub_in_lenv d' T (S n) (U :: e) (lsubst_rec d' U n :: x)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d' U n :: x) g).
apply trunc_S ; auto with coc.
destruct(H2 _ _ _ _ H4 H4 _ _ H31 H32).
apply coerce_env_full with (lsubst_rec d' U n :: x) ; auto.
apply coerce_env_full_cons ; auto with coc.
apply wf_cons with set ; auto.

destruct (H _ _ _ _ H3 H4 _ _ H5 H6).
assert(sub_in_lenv d T (S n) (U' :: e) (lsubst_rec d U' n :: f)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d U' n :: f) g).
apply trunc_S ; auto with coc.
destruct (H2 _ _ _ _ H3 H4 _ _ H9 H10) ; auto with coc.
destruct (H0 _ _ _ _ H3 H4 _ _ H5 H6).
destruct_exists.
destruct (H0 _ _ _ _ H4 H4 _ _ H14 H15).
destruct (H1 _ _ _ _ H4 H4 _ _ H14 H15).
destruct (H1 _ _ _ _ (refl_l H3) (refl_l H3) _ _ H5 H6).

split ; 
apply tposr_coerce_sub_r ; eauto with coc.
apply coerce_env_full with x ; auto with coc.

change (Srt_l prop) with (lsubst_rec d' (Srt_l prop) (S n)).
assert(sub_in_lenv d' T (S n) (U' :: e) (lsubst_rec d' U' n :: x)).
apply sub_S ; auto with coc.
assert(trunc lterm (S n) (lsubst_rec d' U' n :: x) g).
apply trunc_S ; auto with coc.
destruct(H2 _ _ _ _ H4 H4 _ _ H27 H28).
apply coerce_env_full with (lsubst_rec d' U' n :: x) ; auto.
apply coerce_env_full_cons ; auto with coc.
apply wf_cons with set ; auto.
apply coerce_env_full with x ; auto with coc.

destruct (H _ _ _ _ H0 H1 _ _ H2 H3) ; intuition.

destruct (H _ _ _ _ H1 H2 _ _ H3 H4) ;
destruct (H0 _ _ _ _ H1 H2 _ _ H3 H4) ;
destruct (H0 _ _ _ _ (refl_l H1) (refl_l H1) _ _ H3 H4) ;
destruct (H _ _ _ _ (refl_l H1) (refl_l H1) _ _ H3 H4) ;
intuition.

apply tposr_coerce_trans with (lsubst_rec d B n) ; eauto with coc.
apply tposr_coerce_trans with (lsubst_rec d B n) ; eauto with coc.
Qed.

Corollary substitution_tposr_tposr_n : forall g d d' t, g |-- d -> d' : t -> g |-- d' -> d' : t ->
   forall e u v U, e |-- u -> v : U ->
   forall f n, sub_in_lenv d t n e f -> trunc _ n f g -> 
   f |-- (lsubst_rec d u n) -> (lsubst_rec d' v n) : (lsubst_rec d U n).
Proof.
  intros.
  pose (proj1 (ind_substitution_tposr)).
  pose (a _ _ _ _ H1 _ _ _ _ H H0 _ _  H2 H3) ; intuition ; eauto with coc.
Qed.

Corollary substitution_tposr_tposr_wf_n : forall g d d' t, g |-- d -> d' : t -> g |-- d' -> d' : t ->
   forall e, tposr_wf e -> forall f n, sub_in_lenv d t n e f -> 
   trunc _ n f g -> tposr_wf f.
Proof.
  intros.
  pose (proj1 (proj2 (ind_substitution_tposr))).
  pose (a _ H1 _ _ _ _ H H0 _ _  H2 H3) ; intuition ; eauto with coc.
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
