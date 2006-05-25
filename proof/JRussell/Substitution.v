Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import JRussell.Types.
Require Import JRussell.Coercion.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Lemma ind_sub_weak : forall g (d : term) t, g |-= d : t ->
   (forall e u (U : term), e |-= u : U ->
   forall f n, sub_in_env d t n e f -> trunc _ n f g -> 
   f |-= (subst_rec d u n) : (subst_rec d U n)) /\
   (forall e T U s, e |-= T >> U : s ->
   forall f n, sub_in_env d t n e f -> trunc _ n f g -> 
   f |-= (subst_rec d T n) >> (subst_rec d U n) : s) /\
   (forall e U V T, e |-= U = V : T ->
   forall f n, sub_in_env d t n e f -> trunc _ n f g -> 
   f |-= (subst_rec d U n) = (subst_rec d V n) : (subst_rec d T n)).
Proof.
intros g d t H.
apply typ_coerce_jeq_ind with
   (P:=fun e u (U : term) => fun H : e |-= u : U =>
   forall f n, sub_in_env d t n e f -> trunc _ n f g -> 
   f |-= (subst_rec d u n) : (subst_rec d U n)) 
   (P1:=fun e U V T => fun H : e |-= U = V : T =>
   forall f n, sub_in_env d t n e f -> trunc _ n f g -> 
   f |-= (subst_rec d U n) = (subst_rec d V n) : (subst_rec d T n))
   (P0:=fun e T U s => fun H : e |-= T >> U : s =>
   forall f n, sub_in_env d t n e f -> trunc _ n f g -> 
   f |-= (subst_rec d T n) >> (subst_rec d U n) : s) ;
 simpl in |- *;
 intros; auto with coc core arith datatypes.

inversion H0.

inversion H0.

elim (lt_eq_lt_dec n 0); [ intro Hlt_eq | intro Hlt ].
elim Hlt_eq; clear Hlt_eq.
intros.
assert(False) ; try omega ; contradiction.
intros.
rewrite b ; simpl.
rewrite simpl_subst ; auto with arith.
rewrite lift0.
rewrite lift0.
rewrite b in H2.
rewrite b in H1.
inversion H1.
inversion H2.
rewrite <- H3 ; assumption.

inversion H1.
rewrite <- H3 in Hlt.
assert(False) ; try omega ; contradiction.
rewrite commut_lift_subst.
apply type_var with s.
apply H0 ; auto.
rewrite <- H4 in H2.
rewrite <- H5 in H2.
inversion H2 ; auto.

inversion H2.
rewrite simpl_subst ; auto with arith.
rewrite lift0.
rewrite simpl_subst ; auto with arith.
rewrite lift0.
rewrite <- H5 ; assumption.

rewrite commut_lift_subst.
rewrite commut_lift_subst.
rewrite <- H5 in H3.
rewrite <- H6 in H3.
inversion H3.
apply type_weak with s ; auto.

apply type_abs with s1 s2 ; auto with coc.

rewrite distr_subst.
apply type_app with (subst_rec d V n) ; auto with coc.

apply type_pair with s1 s2 s3 ; auto with coc.
rewrite <- distr_subst ; auto with coc.

apply type_prod with s1 ; auto with coc.

apply type_sum with s1 s2 ; auto with coc.

apply type_subset ; auto with coc.

apply type_pi1 with (subst_rec d V (S n)) ; auto with coc.

rewrite distr_subst.
simpl.
apply type_pi2 with (subst_rec d U n) ; auto with coc.

apply type_conv with (subst_rec d U n) s ; auto with coc.

inversion H2.
rewrite simpl_subst ; auto with arith.
rewrite simpl_subst ; auto with arith.
rewrite lift0 ; rewrite lift0.
rewrite <- H5 ; auto.
rewrite <- H5 in H3.
rewrite <- H6 in H3.
inversion H3.

rewrite commut_lift_subst.
rewrite commut_lift_subst.
apply coerce_weak with s' ; auto with coc.

apply coerce_prod with s ; auto with coc.

apply coerce_sum with s s' ; auto with coc.

apply coerce_trans with (subst_rec d B n) ; auto with coc.

inversion H2.
do 3 (rewrite simpl_subst ; auto with arith).
do 3 rewrite lift0.
rewrite <- H5 ; auto.
rewrite <- H5 in H3.
rewrite <- H6 in H3.
inversion H3.

do 3 (rewrite commut_lift_subst).
apply jeq_weak with s ; auto with coc.

apply jeq_prod with s1 ; auto with coc.

apply jeq_abs with s1 s2 ; auto with coc.

rewrite distr_subst.
apply jeq_app with (subst_rec d A n) ; auto with coc.

rewrite distr_subst.
rewrite distr_subst.
apply jeq_beta with s1 s2 ; auto with coc.

apply jeq_red with (subst_rec d A n) s ; auto with coc.

apply jeq_exp with (subst_rec d B n) s ; auto with coc.

apply jeq_sum with s1 s2 ; auto with coc.

apply jeq_pair with s1 s2 s3 ; auto with coc.
simpl.
rewrite <- distr_subst.
apply H3 ; auto with coc.

apply jeq_pi1 with (subst_rec d B (S n)) ; auto with coc.

apply jeq_pi1_red with s1 s2 s3 ; auto with coc.
rewrite <- distr_subst.
apply H3 ; auto with coc.

rewrite distr_subst.
simpl.
apply jeq_pi2 with (subst_rec d A n) ; auto with coc.

rewrite distr_subst.
apply jeq_pi2_red with s1 s2 s3; auto with coc.
rewrite <- distr_subst.
apply H3 ; auto with coc.


apply jeq_subset ; auto with coc.

apply jeq_trans with (subst_rec d N n) ; auto with coc.

apply jeq_conv with (subst_rec d A n) s ; auto with coc.
Qed.

Lemma typ_sub_weak : forall g (d : term) t, g |-= d : t ->
   forall e u (U : term), e |-= u : U ->
   forall f n, sub_in_env d t n e f -> trunc _ n f g -> 
   f |-= (subst_rec d u n) : (subst_rec d U n).
Proof.
  intros g d t H.
  exact (proj1 (ind_sub_weak H)).
Qed.

Lemma coerce_sub_weak : forall g (d : term) t, g |-= d : t ->
   forall e T U s, e |-= T >> U : s ->
   forall f n, sub_in_env d t n e f -> trunc _ n f g -> 
   f |-= (subst_rec d T n) >> (subst_rec d U n) : s.
Proof.
  intros g d t H.
  exact (proj1 (proj2 (ind_sub_weak H))).
Qed.

Lemma jeq_sub_weak : forall g (d : term) t, g |-= d : t ->
   forall e U V T, e |-= U = V : T ->
   forall f n, sub_in_env d t n e f -> trunc _ n f g -> 
   f |-= (subst_rec d U n) = (subst_rec d V n) : (subst_rec d T n).
Proof.
  intros g d t H.
  exact (proj2 (proj2 (ind_sub_weak H))).
Qed.

Theorem substitution : forall e t u U, (t :: e) |-= u : U ->
  forall d, e |-= d : t -> e |-= (subst d u) : (subst d U).
Proof.
intros.
unfold subst in |- *.
destruct (ind_sub_weak H0). 
apply H1 with (t :: e) ; auto with coc core arith datatypes.
Qed.

Theorem substitution_coerce : forall e t T (U : term) s,
  (t :: e) |-= T >> U : s ->
  forall d, e |-= d : t -> e |-= (subst d T) >> (subst d U) : s.
Proof.
intros.
unfold subst in |- *.
destruct (ind_sub_weak H0). 
destruct H2.
apply H2 with (t :: e); auto with coc core arith datatypes.
Qed.

Theorem substitution_jeq : forall e t U V T,
  (t :: e) |-= U = V : T ->
  forall d, e |-= d : t -> e |-= (subst d U) = (subst d V) : subst d T.
Proof.
intros.
unfold subst in |- *.
destruct (ind_sub_weak H0). 
destruct H2.
apply H3 with (t :: e); auto with coc core arith datatypes.
Qed.

Hint Resolve substitution substitution_coerce substitution_jeq : coc.

