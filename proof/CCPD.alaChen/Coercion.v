Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Substitution.


Inductive coerce_in_env : env -> env -> Prop :=
| coerce_env_hd : forall e t u,
  forall s, e |- t : (Srt s) -> e |- u : (Srt s) ->
  e |- t >> u -> coerce_in_env (u :: e) (t :: e)
| coerce_env_tl :
        forall e f t, wf (t :: f) -> coerce_in_env e f -> coerce_in_env (t :: e) (t :: f).

  Hint Resolve coerce_env_hd coerce_env_tl: coc.

  Lemma conv_item :
   forall n t e,
   item_lift t e n ->
   forall f, coerce_in_env e f ->
   item_lift t f n \/
   ((forall g, trunc _ (S n) e g -> trunc _ (S n) f g) /\
   exists u, item_lift u f n /\ (ex2 (fun s => f |- u : (Srt s)) (fun s => f |- t : Srt s) /\
   (wf f -> f |- u >> t))).
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
intros.
split.
inversion_clear H.

exists t0; auto with coc core arith datatypes.

split.
exists s ; auto with coc core.
change (Srt s) with (lift 1 (Srt s)). 
apply thinning_n with l ; auto with coc core.
apply wf_var with s ; auto with coc.

change (Srt s) with (lift 1 (Srt s)). 
apply thinning_n with l ; auto with coc core.
apply wf_var with s ; auto with coc.
apply thinning_n_coerce with l; auto with coc.

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
destruct H7.
exists (lift 1 x0).
split ; auto with coc core.
inversion_clear H6 ; auto with coc core arith.
exists x2.
rewrite H10.
rewrite <- simpl_lift.
auto with coc core.
auto with coc.

split.
exists x1 ; change (Srt x1) with (lift 1 (Srt x1)). 
apply thinning_n with f0 ; auto with coc core.
rewrite simpl_lift.
apply thinning_n with f0 ; auto with coc core.

intros.
pattern (lift (S (S n0)) x).
rewrite simpl_lift.
apply thinning_n_coerce with f0 ; auto with coc arith datatypes.
inversion_clear H6; auto.
pose (typ_wf _ _ _ H7).
apply (H8 w).

exists x; auto with coc core arith datatypes.
Qed.

Lemma typ_conv_env :
  forall e t T, typ e t T -> 
  forall f, coerce_in_env e f -> 
  wf f -> typ f t T.
intros e t T IHt.
induction IHt using typ_mut with 
(P := fun e t T => fun H : typ e t T =>
  forall f, coerce_in_env e f -> 
  wf f -> typ f t T)
(P0 := fun e T U => fun H : e |- T >> U =>
  forall f, coerce_in_env e f -> 
  wf f -> f |- T >> U) ; intros ;
auto with coc core arith datatypes.

elim conv_item with n T e f; auto with coc core arith datatypes; intros.
repeat destruct H1.
destruct H2.
destruct H2.
destruct H3.
destruct H3.
apply type_conv with x x0 ; auto with coc core.

cut (wf (T :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

cut (wf (U :: f)); intros.
apply type_pair with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.

cut (wf (T :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with V ; auto with coc core arith datatypes.

apply type_pi2 with U ; auto with coc core arith datatypes.

cut (wf (U :: f)); intros.
apply type_let_in with U s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.

apply type_conv with U s; auto with coc core arith datatypes.

cut (wf (A' :: f)) ; intros.
apply coerce_prod with s ;auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.

cut (wf (A :: f)) ; intros.
apply coerce_sum with s ;auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.

apply coerce_trans with B s ; auto with coc core arith datatypes.
Qed.

Lemma coerce_conv_env :
  forall e T U, e |- T >> U -> 
  forall f, coerce_in_env e f -> 
  wf f -> f |- T >> U.
intros e t T IHc.
induction IHc using coerce_mut with 
(P := fun e t T => fun H : typ e t T =>
  forall f, coerce_in_env e f -> 
  wf f -> typ f t T)
(P0 := fun e T U => fun H : e |- T >> U =>
  forall f, coerce_in_env e f -> 
  wf f -> f |- T >> U) ; intros ;
auto with coc core arith datatypes.

elim conv_item with n T e f; auto with coc core arith datatypes; intros.
repeat destruct H1.
destruct H2.
destruct H2.
destruct H3.
destruct H3.
apply type_conv with x x0 ; auto with coc core.

cut (wf (T :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

cut (wf (U :: f)); intros.
apply type_pair with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.

cut (wf (T :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with V ; auto with coc core arith datatypes.

apply type_pi2 with U ; auto with coc core arith datatypes.

cut (wf (U :: f)); intros.
apply type_let_in with U s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.

apply type_conv with U s; auto with coc core arith datatypes.

cut (wf (A' :: f)) ; intros.
apply coerce_prod with s ;auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.

cut (wf (A :: f)) ; intros.
apply coerce_sum with s ;auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.

apply coerce_trans with B s ; auto with coc core arith datatypes.
Qed.

Lemma subset_support_not_sort : forall e t T, e |- t : T -> 
  forall U P, t = Subset U P -> 
  forall s, ~ (conv U (Srt s)).
Proof.
  induction 1 ; intros ; try discriminate.

  red ; intros.
  injection H1.
  intros.
  rewrite <- H4 in H2.
Admitted.

Lemma coerce_sort : forall e T U, e |- T >> U ->
  forall r, e |- T : (Srt r) -> e |- U : (Srt r) ->
  forall s,
  (conv T (Srt s) -> conv U (Srt s)) /\ (conv U (Srt s) -> conv T (Srt s)).
Proof.
  induction 1 (*
 using coerce_mut with
  (P := fun e t T => fun H : typ e t T =>
  forall s, T = (Srt s) ->
  forall T', e |- t : T' -> T' = (Srt s))
(P0 := fun e T U => fun H : e |- T >> U =>
  forall r, e |- T : (Srt r) -> e |- U : (Srt r) ->
  forall s,
  (conv T (Srt s) -> conv U (Srt s)) /\ (conv U (Srt s) -> conv T (Srt s))) *); intros ;
auto with coc core arith datatypes ; try discriminate.

  split.
  intros.
  apply trans_conv_conv with A ; auto with coc core.

  intros.
  apply trans_conv_conv with B ; auto with coc core.

(*  injection H.
  intros.
  inversion H0.
  rewrite H1 ; auto.

  destruct (typ_sort H2 (refl_equal (Srt prop))).
  rewrite H10 in H4.
  pose (typ_not_kind H4).
  elim n ; auto.

  injection H.
  intros.
  case (typ_sort H0 (refl_equal (Srt set))).
  intros.
  rewrite <- H1.
  auto with coc.
  
  inversion i.


  induction H0.

  
  Focus 3.

  ssplit ; auto with coc.
  pose (type_subset _ _ t _ t0).
  injection H ; intros.
  rewrite <- H1.
  apply (subset_support_not_sort _ _ _ t1 T U (refl_equal (Subset T U)) s).

  pose (IHcoerce2 s t2 t1).
  pose (IHcoerce U0 P H0).
  destruct a0.
  destruct (a set).
  split.
  apply (H3 H1).
  assumption.
*)
  intuition.
  
  elim (conv_sort_prod s0 A B) ; auto with coc core.
  elim (conv_sort_prod s0 A' B') ; auto with coc core.

  intuition.
  
  elim (conv_sort_sum s0 A B) ; auto with coc core.
  elim (conv_sort_sum s0 A' B') ; auto with coc core.

  intuition.
  
  elim (conv_sort_subset s U P) ; auto with coc core.

  pose (subset_support_not_sort _ _ _ H0 U P (refl_equal (Subset U P)) s).
  
  cut (G |- U : Srt r) ; intros.
  destruct (IHcoerce r H3 H1 s).
  pose (H5 H2).
  contradiction.

  inversion H0 ; auto.
  

  
  Focus 3.
  destruct (IHcoerce1 s H H0 s0).
  destruct (IHcoerce2 s H0 H1 s0).
  split ; intros.
  apply H8 ; auto.

  auto.

  inversion H0.
  rewrite <- H6 in H1.
  induction (IHcoerce _ H7 H1 s).
  pose (H10 H2).
  contradiction.



  
  

  
  

  elim (conv_sort_prod s U P) ; auto with coc core.




Lemma coerce_sym : forall e T U, e |- T >> U ->
  forall s, e |- T : Srt s -> e |- U : Srt s -> 
  e |- U >> T.
Proof.
  intros e T U H ; induction H ; intros ; auto with coc core.
  
  apply coerce_prod with s ; auto with coc.
  apply IHcoerce1 with s ; auto with coc. 
  
  cut (coerce_in_env (A' :: G) (A :: G)).
  cut (coerce_in_env (A :: G) (A' :: G)).
  intros.
  
  apply coerce_conv_env with (A' :: G) ; auto with coc core.
 
  inversion_clear H3.
  apply IHcoerce2 with s0 ; auto with coc.
  
  apply typ_conv_env with (A :: G) ; auto with coc core.
  apply wf_var with s ; auto with coc core.
  
  inversion_clear H4 ; auto with coc core.
  inversion H11.
  apply typ_conv_env with (A :: G) ; auto with coc core.
  apply wf_var with s ; auto with coc core.

  apply coerce_env_

  
