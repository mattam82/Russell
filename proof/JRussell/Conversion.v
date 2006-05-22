Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import JRussell.Types.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Inductive conv_in_env : env -> env -> Prop :=
  | conv_env_hd : forall e t u s, e |- t = u : Srt s -> e |- u : Srt s ->
	conv_in_env (t :: e) (u :: e)
  | conv_env_tl :
      forall e f t, conv_in_env e f -> conv_in_env (t :: e) (t :: f).

Hint Resolve conv_env_hd conv_env_tl: coc.

Lemma double_conv_env :
  (forall e t T, e |- t : T -> 
  forall f, conv_in_env e f -> f |- t : T) /\
  (forall e T U s, e |- T >> U : s -> 
  forall f, conv_in_env e f -> f |- T >> U : s) /\
  (forall e U V T, e |- U = V : T ->
  forall f, conv_in_env e f -> f |- U = V : T) /\
  (forall e, wf e ->
  forall f, conv_in_env e f -> wf f /\
  (forall n t,
  item_lift t e n ->
  (item_lift t f n \/
   (exists u, item_lift u f n /\ (exists s, f |- u = t : Srt s /\ f |- t : Srt s))))).
Proof.
apply typ_coerce_jeq_wf_ind with 
(P := fun e t T => fun H : typ e t T =>
  forall f, conv_in_env e f -> 
  typ f t T)
(P0 := fun e T U s => fun H : e |- T >> U : s =>
  forall f, conv_in_env e f -> 
  f |- T >> U : s) 
(P1 := fun e U V T => fun H : e |- U = V : T =>
  forall f, conv_in_env e f -> 
  f |- U = V : T)
(P2 := fun e => fun H : wf e =>
  forall f, conv_in_env e f -> wf f /\
  (forall n t,
  item_lift t e n ->
  item_lift t f n \/
   (exists u, item_lift u f n /\ (exists s, f |- u = t : Srt s /\ f |- t : Srt s))));
 intros ; try (destruct (H f H0) ; clear H); 
auto with coc core arith datatypes.

elim H2 with n T; auto with coc core arith datatypes; intros.
destruct H.
destruct H.
destruct H3.
destruct H3.
apply type_conv with x x0 ; auto with coc core.

cut (wf (T :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.
pose (H _ H2).
apply wf_var with s1; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

cut (wf (U :: f)); intros.
apply type_pair with s1 s2 s3; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.

cut (wf (T :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T :: f)); intros.
apply type_sum with s1 s2; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with V ; auto with coc core arith datatypes.

apply type_pi2 with U ; auto with coc core arith datatypes.

(*cut (wf (U :: f)); intros.
apply type_let_in with U s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.*)

apply type_conv with U s; auto with coc core arith datatypes.

cut (wf (A' :: f)) ; intros.
cut (wf (A :: f)) ; intros.
apply coerce_prod with s ;auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.

cut (wf (A' :: f)) ; intros.
cut (wf (A :: f)) ; intros.
apply coerce_sum with s s' ;auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.
(*
apply coerce_sub_l ; auto with coc core arith datatypes.
apply H2 ; auto with coc.
constructor ; auto.
eapply wf_var ; auto with coc core arith datatypes.

cut (wf (U' :: f)) ; intros.
apply coerce_sub_r ; auto with coc core arith datatypes.
eapply wf_var ; auto with coc core arith datatypes.
*)
apply coerce_conv with B C ; auto with coc core arith datatypes.

(* jeq *)
apply jeq_prod with s1 ; auto with coc.

apply jeq_abs with s1 s2 ; auto with coc.

apply jeq_app with A ; auto with coc.

apply jeq_beta with s1 s2 ; auto with coc.

apply jeq_conv with A s ; auto with coc.

apply jeq_conv with B s ; auto with coc.

apply jeq_sum with s1 s2 ; auto with coc.

apply jeq_pi1 with A' s1 B B' s2 s3 ; auto with coc.

apply jeq_pi1_red with A' s1 B' s2 s3 u' v'; auto with coc.

apply jeq_pi2 with A A' s1 B' s2 s3 ; auto with coc.

apply jeq_pi2_red with A' s1 B' s2 s3 u' v'; auto with coc.

apply jeq_subset; auto with coc.

apply jeq_trans with N; auto with coc.

apply jeq_conv with A s; auto with coc.

inversion H.
inversion H0.
split ; intros.
apply wf_var with s0 ; auto with coc.
right.
rewrite H4.



apply H0.
constructor ; auto.


apply wf_var with s1.


Qed.

(*Lemma conv_item :
   forall n t e,
   item_lift t e n ->
   forall f, conv_in_env e f ->
   item_lift t f n \/
   ((forall g, trunc _ (S n) e g -> trunc _ (S n) f g) /\
   exists u, item_lift u f n /\ (exists s, f |- u = t : Srt s)).
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

exists (lift 1 t0).
split.
inversion_clear H.

unfold item_lift.
exists t0; auto with coc core arith datatypes.

exists s ; auto with coc core.
apply thinning_n_coerce with l ; auto with coc core.
apply wf_var with s.
apply coerce_sort_l with x ; auto with coc.

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

elim H with (lift (S n0) x) l f0; auto with coc core arith datatypes; intros.
left.
elim H2; intros.
exists x0; auto with coc core arith datatypes.
rewrite simpl_lift.
pattern (lift (S (S n0)) x0) in |- *.
rewrite simpl_lift.
elim H6; auto with coc core arith datatypes.

right.
elim H2.
clear H2.
simple induction 2; intros.
clear H6.
split; intros.
inversion_clear H6; auto with coc core arith datatypes.

destruct H7.
destruct H7.
unfold item_lift.
exists (lift 1 x0).
split ; auto with coc core.
inversion_clear H6 ; auto with coc core arith.
exists x2.
rewrite H8.
rewrite <- simpl_lift.
auto with coc core.
auto with coc.

exists x1.
pattern (lift (S (S n0)) x) ; rewrite simpl_lift.
eapply thinning_n_coerce ; auto with coc core.

exists x; auto with coc core arith datatypes.
Qed.
*)
