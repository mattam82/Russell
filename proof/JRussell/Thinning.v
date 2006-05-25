Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.Conv.
Require Import JRussell.Types.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Lemma type_weak_lift_rec : forall e t T, e |-= t : T -> forall A s, e |-= A : Srt s ->
  (A :: e) |-= lift_rec 1 t 0 : lift_rec 1 T 0. 
Proof.
  intros.
  pose (type_weak H H0).
  unfold lift in t0.
  apply t0.
Qed.

Lemma coerce_weak_lift_rec : forall e T U s, e |-= T >> U : s -> forall A s', e |-= A : Srt s' ->
  (A :: e) |-= lift_rec 1 T 0 >> lift_rec 1 U 0 : s. 
Proof.
  intros.
  pose (coerce_weak H H0).
  unfold lift in c.
  apply c.
Qed.

Lemma jeq_weak_lift_rec : forall e t u T, e |-= t = u : T -> forall A s, e |-= A : Srt s ->
  (A :: e) |-= lift_rec 1 t 0 = lift_rec 1 u 0 : lift_rec 1 T 0. 
Proof.
  intros.
  pose (jeq_weak H H0).
  unfold lift in j.
  apply j.
Qed.

Hint Resolve type_weak_lift_rec : coc.

Lemma ind_weak_weak : forall g A s, g |-= A : Srt s ->
  (forall e t T, e |-= t : T ->
   forall n f, ins_in_env A n e f ->
   trunc _ n e g ->
   f |-= (lift_rec 1 t n) : (lift_rec 1 T n)) /\
 (forall e T U s, e |-= T >> U : s ->
  forall n f, ins_in_env A n e f ->
  trunc _ n e g ->
  f |-= (lift_rec 1 T n) >> (lift_rec 1 U n) : s) /\
 (forall e U V T, e |-= U = V : T ->
  forall n f, ins_in_env A n e f ->
  trunc _ n e g ->
  f |-= (lift_rec 1 U n) = (lift_rec 1 V n) : (lift_rec 1 T n)).
Proof.
intros g A As HAs.
apply typ_coerce_jeq_ind with 
 (P := fun e t T => fun IH : typ e t T =>
   forall n f, ins_in_env A n e f ->
   trunc _ n e g -> 
   f |-= (lift_rec 1 t n) : (lift_rec 1 T n))
 (P0 := fun e T U s => fun IH : coerce e T U s =>
  forall n f, ins_in_env A n e f ->
  trunc _ n e g ->
  f |-= (lift_rec 1 T n) >> (lift_rec 1 U n) : s)
 (P1 := fun e U V T => fun IH : e |-= U = V : T =>
  forall n f, ins_in_env A n e f ->
  trunc _ n e g -> 
  f |-= (lift_rec 1 U n) = (lift_rec 1 V n) : (lift_rec 1 T n)) ; 
  intros ; try simpl in H ; try simpl in H0 ; try simpl in H1 ; try simpl in H2 ; try simpl in H3 ; 
  try simpl in H4 ; 
  auto with coc core arith datatypes.
(* Prop *)
inversion H.
inversion H0.
rewrite <- H6 in HAs.
apply type_weak_lift_rec with As ; auto with coc.

(* Set *)
inversion H.
inversion H0.
rewrite <- H6 in HAs.
apply type_weak_lift_rec with As ; auto with coc.

(* Var *)
inversion H0.
rewrite <- H2 in H1.
inversion H1.
apply type_weak_lift_rec with As ; auto with coc.
apply type_var with s ; auto with coc.
rewrite H7 ; assumption.

simpl.
rewrite <- permute_lift.
apply type_var with s ; auto with coc.
simpl in H.
rewrite <- H3 in H1.
inversion H1.
apply H ; auto with coc.

(* Weak *)
inversion H1.
rewrite <- H3 in H2.
inversion H2.
apply type_weak_lift_rec with As ; auto with coc.
apply type_weak with s ; auto with coc.
rewrite H8 ; assumption.
rewrite <- H4 in H2.
inversion H2.
rewrite <- permute_lift.
rewrite <- permute_lift.
apply type_weak with s ; auto with coc.

(* Abs *)
simpl.
apply type_abs with s1 s2 ; auto with coc.

(* App *)
simpl.
rewrite distr_lift_subst.
apply type_app with (lift_rec 1 V n) ; auto with coc.

(* Pair *)
simpl.
apply type_pair with s1 s2 s3 ; auto with coc.
rewrite <- distr_lift_subst ; auto with coc.

(* Prod *)
simpl.
apply type_prod with s1 ; auto with coc.

(* Sum *)
simpl.
apply type_sum with s1 s2 ; auto with coc.

(* Subset *)
simpl.
apply type_subset ; auto with coc.

(* Pi1 *)
simpl.
apply type_pi1 with (lift_rec 1 V (S n)) ; auto with coc.

(* Pi2 *)
simpl.
rewrite distr_lift_subst.
simpl.
apply type_pi2 with (lift_rec 1 U n) ; auto with coc.

(* Conv *)
apply type_conv with (lift_rec 1 U n) s ; auto with coc.

(** coercion *)
(* Conv done *)

(* Weak *)
inversion H1.
rewrite <- H3 in H2.
inversion H2.
apply coerce_weak_lift_rec with As ; auto with coc.
apply coerce_weak with s' ; auto with coc.
rewrite H8 ; assumption.
rewrite <- H4 in H2.
inversion H2.
rewrite <- permute_lift.
rewrite <- permute_lift.
apply coerce_weak with s' ; auto with coc.

(* Prod *)
simpl.
apply coerce_prod with s ; auto with coc.

(* Sum *)
simpl.
apply coerce_sum with s s' ; auto with coc.

(* Subset left *)
simpl.
apply coerce_sub_l ; auto with coc.

(* Subset right *)
simpl.
apply coerce_sub_r ; auto with coc.

(* Sym done *)

(* Trans *)
apply coerce_trans with (lift_rec 1 B n) ; auto with coc.

(** Judgemental equality *)
(* Weak *)
inversion H1.
rewrite <- H3 in H2.
inversion H2.
apply jeq_weak_lift_rec with As ; auto with coc.
apply jeq_weak with s ; auto with coc.
rewrite H8 ; assumption.
rewrite <- H4 in H2.
inversion H2.
do 3 rewrite <- permute_lift.
apply jeq_weak with s ; auto with coc.

(* Prod *)
simpl ; apply jeq_prod with s1 ; auto with coc.

(* Abs *)
simpl ; apply jeq_abs with s1 s2 ; auto with coc.

(* App *)
rewrite distr_lift_subst.
simpl ; apply jeq_app with (lift_rec 1 A0 n) ; auto with coc.

(* Beta *)
do 2 rewrite distr_lift_subst.
simpl ; apply jeq_beta with s1 s2 ; auto with coc.

(* Red *)
apply jeq_red with (lift_rec 1 A0 n) s ; auto with coc.

(* Exp *)
apply jeq_exp with (lift_rec 1 B n) s ; auto with coc.

(* Sum *)
simpl ; apply jeq_sum with s1 s2 ; auto with coc.

(* Pair *)
simpl ; apply jeq_pair with s1 s2 s3 ; auto with coc.
simpl.
rewrite <- distr_lift_subst.
apply H2 ; auto with coc.

(* Pi1 *)
simpl ; apply jeq_pi1 with (lift_rec 1 B (S n)) ; auto with coc.

(* Pi1 red *)
simpl ; apply jeq_pi1_red with s1 s2 s3 ; auto with coc.
rewrite <- distr_lift_subst.
apply H2 ; auto with coc.

(* Pi2 *)
rewrite distr_lift_subst.
simpl ; apply jeq_pi2 with (lift_rec 1 A0 n) ; auto with coc.

(* Pi2 red *)
rewrite distr_lift_subst.
simpl ; apply jeq_pi2_red with s1 s2 s3; auto with coc.
rewrite <- distr_lift_subst.
apply H2 ; auto with coc.

(* Subset *)
simpl ; apply jeq_subset ; auto with coc.

(* Trans *)
simpl; apply jeq_trans with (lift_rec 1 N n) ; auto with coc.

(* Conv *)
simpl ; apply jeq_conv with (lift_rec 1 A0 n) s ; auto with coc.
Qed.

Lemma type_weak_weak : forall g A s, g |-= A : Srt s ->
  forall e t T, e |-= t : T ->
   forall n f, ins_in_env A n e f ->
   trunc _ n e g ->
   f |-= (lift_rec 1 t n) : (lift_rec 1 T n).
Proof.
  intros g A s H.
  exact (proj1 (ind_weak_weak H)).
Qed.

Lemma coerce_weak_weak : forall g A s, g |-= A : Srt s ->
  forall e T U s, e |-= T >> U : s ->
  forall n f, ins_in_env A n e f ->
  trunc _ n e g ->
  f |-= (lift_rec 1 T n) >> (lift_rec 1 U n) : s.
Proof.
  intros g A s H.
  exact (proj1 (proj2 (ind_weak_weak H))).
Qed.

Lemma jeq_weak_weak : forall g A s, g |-= A : Srt s ->
  forall e U V T, e |-= U = V : T ->
  forall n f, ins_in_env A n e f ->
  trunc _ n e g ->
  f |-= (lift_rec 1 U n) = (lift_rec 1 V n) : (lift_rec 1 T n).
Proof.
  intros g A s H.
  exact (proj2 (proj2 (ind_weak_weak H))).
Qed.

Lemma thinning_n :
   forall n e f,
   trunc _ n e f ->
   consistent e ->
   forall t T, typ f t T -> typ e (lift n t) (lift n T).
Proof.
simple induction n.
intros.
rewrite lift0.
rewrite lift0.
replace e with f; auto with coc core arith datatypes.
inversion_clear H; auto with coc core arith datatypes.

do 8 intro.
inversion H0.
intro.
rewrite simpl_lift; auto with coc core arith datatypes.
pattern (lift (S n0) T) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
rewrite <- H4 in H1.
inversion H1.
apply type_weak with s ; auto with coc.
apply H with f ; auto.
Qed.

Lemma thinning_n_coerce : forall n e f, trunc _ n e f -> 
  forall T U s, f |-= T >> U : s -> consistent e -> e |-= (lift n T) >> (lift n U) : s.
Proof.
simple induction n.
intros.
rewrite lift0.
rewrite lift0.
replace e with f; auto with coc core arith datatypes.
inversion_clear H; auto with coc core arith datatypes.

do 9 intro.
inversion_clear H0.
intro.
rewrite simpl_lift; auto with coc core arith datatypes.
pattern (lift (S n0) T) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
inversion_clear H0.
replace (lift (S n0) U) with (lift 1 (lift n0 U)).
apply coerce_weak with s0 ; auto with coc.
eapply H with f ; auto with coc core arith datatypes.
rewrite <- simpl_lift.
auto.
Qed.

Hint Resolve thinning_n thinning_n_coerce : coc.

Lemma item_ref_lift :
 forall n e t, item _ t e n -> consistent e -> e |-= Ref n : lift (S n) t.
simple induction n ; intros.
inversion H.
rewrite <- H1 in H0.
inversion H0.
apply type_var with s ; auto.

inversion H0.
change (Ref (S n0)) with (lift 1 (Ref n0)).
replace (lift (S (S n0)) (t)) with (lift 1 (lift (S n0) t)).
apply thinning_n with l ; try constructor ; auto with coc.
rewrite H3 ; auto.
apply H ; auto.
rewrite <- H3 in H1.
inversion H1.
auto.
rewrite <- simpl_lift.
reflexivity.
Qed.

(*Lemma item_sorted_lift :
 forall e n t, item _ t e n -> 
 forall f, trunc _ n e f -> exists s : sort, f |-= t : (Srt s).
intros e u V H.
simple induction n ; intros.

inversion H0.
rewrite <- H2 in H1.
inversion H1.
rewrite <- H2 in H.
inversion H.
exists 

simple destruct e; intros.
elim H0; intros.
inversion_clear H2.

elim H0; intros.
rewrite H1.
inversion_clear H2.
inversion_clear H.
exists s.
replace (Srt s) with (lift 1 (Srt s)); auto with coc core arith datatypes.
apply thinning; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.

intros.
elim H1; intros.
rewrite H2.
generalize H0.
inversion_clear H3; intros.
rewrite simpl_lift; auto with coc core arith datatypes.
cut (wf l); intros.
elim H with l (lift (S n0) x); intros; auto with coc core arith datatypes.
inversion_clear H3.
exists x0.
change (typ (y :: l) (lift 1 (lift (S n0) x)) (lift 1 (Srt x0))) in |- *.
apply thinning; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.

inversion_clear H3.
apply typ_wf with y (Srt s); auto with coc core arith datatypes.
Qed.


*)