Require Import Lambda.Tactics.
Require Import Lambda.Utils.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.TypesNoDerivs.
Require Import Lambda.TPOSR.Thinning.
Require Import Lambda.TPOSR.LeftReflexivity.


Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Inductive exp_in_env : lenv -> lenv -> Prop :=
  | exp_env_hd : forall e t u s, e |-- t -> u : Srt_l s -> e |-- u -> u : Srt_l s ->
	exp_in_env (u :: e) (t :: e)
  | exp_env_tl :
      forall e f t, exp_in_env e f -> 
      tposr_wf (t :: e) ->
      exp_in_env (t :: e) (t :: f).

Hint Resolve exp_env_hd exp_env_tl: coc.

Lemma exp_item :
   forall n t e,
   item_llift t e n ->
   forall f, exp_in_env e f ->
   item_llift t f n \/
   ((forall g, trunc _ (S n) e g -> trunc _ (S n) f g) /\
   exists u, item_llift u f n /\ (exists s : sort, tposr_wf f -> f |-- u -> t : s)).
simple induction n.
do 3 intro.
elim H.
do 4 intro.
rewrite H0.
inversion_clear H1.
intros.
inversion_clear H1.
right.
split; intros.
inversion_clear H1; auto with coc core arith datatypes.

exists (llift 1 t0).
split.
inversion_clear H.

unfold item_llift.
exists t0; auto with coc core arith datatypes.

exists s ; auto with coc core.
change (Srt_l s) with (llift 1 (Srt_l s)).
apply thinning_n with l ; auto with coc core ;
apply wf_cons with u s ; auto.

left.
exists x; auto with coc core arith datatypes.

do 5 intro.
elim H0.
do 4 intro.
rewrite H1.
inversion_clear H2.
intros.
inversion_clear H2.
left.
exists x; auto with coc core arith datatypes.

elim H with (llift (S n0) x) l f0; auto with coc core arith datatypes; intros.
left.
elim H2; intros.
exists x0; auto with coc core arith datatypes.
rewrite simpl_llift.
pattern (llift (S (S n0)) x0) in |- *.
rewrite simpl_llift.
rewrite H6; auto with coc core arith datatypes.

right.
elim H2.
clear H2.
simple induction 2; intros.
clear H7.
split; intros.
inversion_clear H7; auto with coc core arith datatypes.

destruct H6.
destruct H6.
destruct H7.
unfold item_llift.
exists (llift 1 x1).
split ; auto with coc core.
inversion_clear H6 ; auto with coc core arith.
exists x3.
rewrite H8.
rewrite <- simpl_llift.
auto with coc core.
auto with coc.

exists x2.
pattern (llift (S (S n0)) x) ; rewrite simpl_llift.
change (Srt_l x2) with (llift 1 (Srt_l x2)).
destruct H6.
intros.
eapply thinning_n ; auto with coc core.
apply H7.
inversion H9 ; auto.
subst.
apply (wf_tposr H11). 
(*apply wf_cons with A' s ; auto.
subst.*)

exists x; auto with coc core arith datatypes.
Qed.

Lemma ind_exp_env :
  (forall e t u T, e |-- t -> u : T -> 
  forall f, exp_in_env e f -> f |-- t -> u : T) /\
  (forall e, tposr_wf e -> 
  forall f, exp_in_env e f -> tposr_wf f) /\
  (forall e t u s, e |-- t ~= u : s -> 
  forall f, exp_in_env e f -> f |-- t ~= u : s) /\
  (forall e t u s, e |-- t >-> u : s -> 
  forall f, exp_in_env e f -> f |-- t >-> u : s).
Proof.
  apply ind_tposr_wf_eq_coerce with
  (P:=fun e t u T => fun H : e |-- t -> u : T => 
  forall f, exp_in_env e f -> f |-- t -> u : T) 
  (P0:=fun e => fun H : tposr_wf e => 
  forall f, exp_in_env e f -> tposr_wf f) 
  (P1:=fun e t u s => fun H : e |-- t ~= u : s => 
  forall f, exp_in_env e f -> f |-- t ~= u : s) 
  (P2:=fun e t u s => fun H : e |-- t >-> u : s => 
  forall f, exp_in_env e f -> f |-- t >-> u : s) ;
  intros ; 
auto with coc core arith datatypes.

destruct (exp_item i H0) ; destruct_exists.
apply tposr_var ; auto with coc.
apply tposr_conv with x x0 ; auto with coc.
pose (H3 (H _ H0)).
eauto with coc ecoc.

apply tposr_prod with s1 ; eauto with coc ecoc.

apply tposr_abs with s1 B' s2 ; eauto with coc ecoc.

apply tposr_app with A A' s1 s2 ; eauto with coc ecoc.

apply tposr_beta with A' s1 B' s2 ; eauto with coc ecoc.

apply tposr_conv with A s ; auto with coc.

apply tposr_subset ; eauto with coc ecoc.

apply tposr_sum with s1 s2 ; eauto with coc ecoc.

apply tposr_pair with s1 s2 s3 ; eauto with coc ecoc.

apply tposr_pi1 with s1 s2 s3 ; eauto with coc ecoc.

apply tposr_pi1_red with A' s1 B' s2 s3 v' ; eauto with coc ecoc.

apply tposr_pi2 with s1 s2 s3 ; eauto with coc ecoc.

apply tposr_pi2_red with A' s1 B' s2 s3 u' ; eauto with coc ecoc.

inversion H.
inversion H0.
subst.
apply wf_cons with A s0 ; auto.
subst.
apply wf_cons with A' s ; eauto with coc ecoc.

apply tposr_eq_trans with X ; auto with coc.

apply tposr_coerce_prod with s ; eauto with coc ecoc.

apply tposr_coerce_sum with s s' ; eauto with coc ecoc.

apply tposr_coerce_sub_l  ; eauto with coc ecoc.

apply tposr_coerce_sub_r  ; eauto with coc ecoc.

apply tposr_coerce_trans with B ; auto with coc ecoc.
Qed.

Lemma tposr_exp_env : forall e t u T, e |-- t -> u : T -> 
  forall f, exp_in_env e f -> f |-- t -> u : T.
Proof (proj1 ind_exp_env).

Lemma eq_exp_env : forall e u v s, e |-- u ~= v : s ->
  forall f, exp_in_env e f -> f |-- u ~= v : s.
Proof (proj1 (proj2 (proj2 ind_exp_env))).

Lemma coerce_exp_env : forall e T U s, e |-- T >-> U : s -> 
  forall f, exp_in_env e f -> f |-- T >-> U : s.
Proof (proj2 (proj2 (proj2 ind_exp_env))).

Hint Resolve tposr_exp_env eq_exp_env coerce_exp_env : ecoc.
