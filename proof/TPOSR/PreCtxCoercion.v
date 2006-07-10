Require Import Lambda.Tactics.
Require Import Lambda.Utils.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Thinning.
Require Import Lambda.TPOSR.LeftReflexivity.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Inductive pre_coerce_in_env : lenv -> lenv -> Prop :=
  | pre_coerce_env_hd : forall e t u s, e |-- t >-> u : s -> e |-- t -> t : s -> e |-- u -> u : Srt_l s ->
	pre_coerce_in_env (t :: e) (u :: e)
  | pre_coerce_env_tl :
      forall e f t, pre_coerce_in_env e f -> 
      forall s, f |-- t -> t : Srt_l s ->
      pre_coerce_in_env (t :: e) (t :: f).

Hint Resolve pre_coerce_env_hd pre_coerce_env_tl: coc.

Lemma coerce_item :
   forall n t e,
   item_llift t e n ->
   forall f, pre_coerce_in_env e f ->
   item_llift t f n \/
   ((forall g, trunc _ (S n) e g -> trunc _ (S n) f g) /\
   exists u, item_llift u f n /\ (exists s : sort, f |-- t >-> u : s /\ f |-- u -> u : s)).
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

exists (llift 1 u).
split.
inversion_clear H.

unfold item_llift.
exists u; auto with coc core arith datatypes.

exists s ; auto with coc core.
change (Srt_l s) with (llift 1 (Srt_l s)).
split.
apply thinning_n_coerce with l ; auto with coc core ;
apply wf_cons with s ; eauto with coc.
apply thinning_n with l ; auto with coc core ;
apply wf_cons with s ; auto.

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
destruct H7.
split.
eapply thinning_n_coerce ; auto with coc core ;
apply wf_cons with s ; auto.
eapply thinning_n ; auto with coc core ;
apply wf_cons with s ; auto.

exists x; auto with coc core arith datatypes.
Qed.

Lemma ind_pre_coerce_env :
  (forall e t u T, e |-- t -> u : T -> 
  forall f, pre_coerce_in_env e f -> f |-- t -> u : T) /\
  (forall e, tposr_wf e -> 
  forall f, pre_coerce_in_env e f -> tposr_wf f) /\
  (forall e t u s, e |-- t ~= u : s -> 
  forall f, pre_coerce_in_env e f -> f |-- t ~= u : s) /\
  (forall e t u s, e |-- t >-> u : s -> 
  forall f, pre_coerce_in_env e f -> f |-- t >-> u : s).
Proof.
  apply ind_tposr_wf_eq_coerce with
  (P:=fun e t u T => fun H : e |-- t -> u : T => 
  forall f, pre_coerce_in_env e f -> f |-- t -> u : T) 
  (P0:=fun e => fun H : tposr_wf e => 
  forall f, pre_coerce_in_env e f -> tposr_wf f) 
  (P1:=fun e t u s => fun H : e |-- t ~= u : s => 
  forall f, pre_coerce_in_env e f -> f |-- t ~= u : s) 
  (P2:=fun e t u s => fun H : e |-- t >-> u : s => 
  forall f, pre_coerce_in_env e f -> f |-- t >-> u : s) ;
  intros ; 
auto with coc core arith datatypes.

destruct (coerce_item i H0) ; destruct_exists.
apply tposr_var ; auto with coc.
apply tposr_conv with x x0.
apply tposr_var.
apply (H _ H0).
assumption.
apply tposr_coerce_sym.
assumption.

apply tposr_prod with s1 ; eauto with coc.

apply tposr_abs with s1 B' s2 ; eauto with coc.

apply tposr_app with A A' s1 s2 ; eauto with coc.

apply tposr_beta with A' s1 B' s2 ; eauto with coc.

apply tposr_conv with A s ; auto with coc.

apply tposr_subset ; eauto with coc.

apply tposr_sum with s1 s2 ; eauto with coc.

apply tposr_pair with s1 s2 s3 ; eauto with coc.

apply tposr_pi1 with s1 s2 s3 ; eauto with coc.

eapply tposr_pi1_red ; eauto with coc.

apply tposr_pi2 with s1 s2 s3 ; eauto with coc.

eapply tposr_pi2_red  ; eauto with coc.

inversion H.
inversion H0.
subst.
apply wf_cons with s0 ; auto.
apply wf_cons with s0 ; auto.

apply tposr_eq_trans with X ; auto with coc.

apply tposr_coerce_prod with s ; eauto with coc.

apply tposr_coerce_sum with s s' ; eauto with coc.

apply tposr_coerce_sub_l  ; eauto with coc.

apply tposr_coerce_sub_r  ; eauto with coc.

apply tposr_coerce_trans with B ; auto with coc.
Qed.

Lemma tposr_pre_coerce_env : forall e t u T, e |-- t -> u : T -> 
  forall f, pre_coerce_in_env e f -> f |-- t -> u : T.
Proof (proj1 ind_pre_coerce_env).

Lemma eq_pre_coerce_env : forall e u v s, e |-- u ~= v : s ->
  forall f, pre_coerce_in_env e f -> f |-- u ~= v : s.
Proof (proj1 (proj2 (proj2 ind_pre_coerce_env))).

Lemma coerce_pre_coerce_env : forall e T U s, e |-- T >-> U : s -> 
  forall f, pre_coerce_in_env e f -> f |-- T >-> U : s.
Proof (proj2 (proj2 (proj2 ind_pre_coerce_env))).

Hint Resolve tposr_pre_coerce_env eq_pre_coerce_env coerce_pre_coerce_env : ecoc.

Inductive pre_coerce_in_env_full : lenv -> lenv -> Prop :=
  | pre_coerce_env_trans : forall e f g, pre_coerce_in_env_full e f -> pre_coerce_in_env_full f g -> pre_coerce_in_env_full e g
  | pre_coerce_env_in_env : forall e f, pre_coerce_in_env e f -> pre_coerce_in_env_full e f
  | pre_coerce_env_nil : pre_coerce_in_env_full nil nil.

Hint Resolve pre_coerce_env_in_env pre_coerce_env_nil : coc.

Lemma pre_coerce_env_sym : forall e f, pre_coerce_in_env e f -> pre_coerce_in_env f e.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  apply pre_coerce_env_hd with s ; eauto with coc.
  apply pre_coerce_env_tl with s ; eauto with coc.
  apply tposr_pre_coerce_env with f ; auto.
Qed.  

Lemma pre_coerce_env_full_sym : forall e f, pre_coerce_in_env_full e f -> pre_coerce_in_env_full f e.
Proof.
  induction 1 ; simpl ; intros ; eauto with coc.
  apply pre_coerce_env_trans with f ; auto.
  apply pre_coerce_env_in_env ; auto.
  apply pre_coerce_env_sym ; auto.
Qed.

Hint Resolve pre_coerce_env_sym pre_coerce_env_full_sym : coc.

Lemma pre_coerce_env_full :
  (forall e t u T, e |-- t -> u : T -> 
  forall f, pre_coerce_in_env_full e f -> f |-- t -> u : T).
Proof.
  intros.
  induction H0 ; auto.

  apply tposr_pre_coerce_env with e ; auto with coc.
Qed.

Lemma pre_coerce_env_full_cons : forall G D, pre_coerce_in_env_full G D -> forall T, tposr_wf (T :: G) ->
  pre_coerce_in_env_full (T :: G) (T :: D).
Proof.
  induction 1 ; simpl ; intros.
  apply pre_coerce_env_trans with (T :: f) ; eauto with coc.
  apply IHpre_coerce_in_env_full2.
  inversion H1.
  apply wf_cons with  s.
  apply pre_coerce_env_full with e ; auto with coc.

  inversion H0.
  subst.
  apply pre_coerce_env_in_env ; eauto with coc.

  apply pre_coerce_env_in_env ; auto with coc.
  inversion H.
  assert(nil |-- T -> T : s).
  eauto with coc.
  apply pre_coerce_env_hd with s ; auto with coc.
Qed.

Corollary tposrp_pre_coerce_env_full : 
  (forall e t u T, e |-- t -+> u : T -> 
  forall f, pre_coerce_in_env_full e f -> f |-- t -+> u : T).
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  apply tposrp_tposr ; eapply pre_coerce_env_full ; eauto with coc.
  apply tposrp_trans with X ; auto with coc.
Qed.

Corollary eq_pre_coerce_env_full : 
  (forall e t u s, e |-- t ~= u : s -> 
  forall f, pre_coerce_in_env_full e f -> f |-- t ~= u : s).
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  apply tposr_eq_tposr ; eapply pre_coerce_env_full ; eauto with coc.
  apply tposr_eq_trans with X ; auto with coc.
Qed.

Hint Resolve pre_coerce_env_full eq_pre_coerce_env_full : ecoc.

Corollary coerce_pre_coerce_env_full : 
  (forall e t u s, e |-- t >-> u : s -> 
  forall f, pre_coerce_in_env_full e f -> f |-- t >-> u : s).
Proof.
  induction 1 ; simpl ; intros ; auto with coc.

  apply tposr_coerce_conv ; eapply eq_pre_coerce_env_full ; eauto with coc.

  assert(pre_coerce_in_env_full (A' :: e) (A' :: f)) by
  (apply pre_coerce_env_full_cons ; auto with coc;
  eauto with coc ecoc).
  assert(pre_coerce_in_env_full (A :: e) (A :: f)) by
  (apply pre_coerce_env_full_cons ; auto with coc;
  eauto with coc ecoc).
  apply tposr_coerce_prod with s ; eauto with coc ecoc.

  assert(pre_coerce_in_env_full (A' :: e) (A' :: f)) by
  (apply pre_coerce_env_full_cons ; auto with coc;
  eauto with coc ecoc).
  assert(pre_coerce_in_env_full (A :: e) (A :: f)) by
  (apply pre_coerce_env_full_cons ; auto with coc;
  eauto with coc ecoc).
  apply tposr_coerce_sum with s s' ; eauto with coc ecoc.

  assert(pre_coerce_in_env_full (U :: e) (U :: f)) by
  (apply pre_coerce_env_full_cons ; auto with coc;
  eauto with coc ecoc).
  apply tposr_coerce_sub_l ; eauto with coc ecoc.

  assert(pre_coerce_in_env_full (U' :: e) (U' :: f)) by
  (apply pre_coerce_env_full_cons ; auto with coc ; eauto with coc ecoc).
  apply tposr_coerce_sub_r ; eauto with coc ecoc.
  
  apply tposr_coerce_trans with B ; auto.
Qed.

