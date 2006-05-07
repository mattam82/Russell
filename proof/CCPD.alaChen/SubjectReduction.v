Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Substitution.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

  Inductive red1_in_env : env -> env -> Prop :=
    | red1_env_hd : forall e t u, red1 t u -> red1_in_env (t :: e) (u :: e)
    | red1_env_tl :
        forall e f t, red1_in_env e f -> red1_in_env (t :: e) (t :: f).

  Hint Resolve red1_env_hd red1_env_tl: coc.
  Lemma red_item :
   forall n t e,
   item_lift t e n ->
   forall f,
   red1_in_env e f ->
   item_lift t f n \/
   (forall g, trunc _ (S n) e g -> trunc _ (S n) f g) /\
   ex2 (fun u => red1 t u) (fun u => item_lift u f n).
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

exists (lift 1 u).
unfold lift in |- *; auto with coc core arith datatypes.

exists u; auto with coc core arith datatypes.

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
elim H5; auto with coc core arith datatypes.

right.
elim H2.
simple induction 2; intros.
split; intros.
inversion_clear H9; auto with coc core arith datatypes.

elim H8; intros.
exists (lift (S (S n0)) x1).
rewrite simpl_lift.
pattern (lift (S (S n0)) x1) in |- *.
rewrite simpl_lift.
elim H9; unfold lift at 1 3 in |- *; auto with coc core arith datatypes.

exists x1; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.
Qed.


Lemma typ_red_env :
 forall e t T, typ e t T -> forall f, red1_in_env e f -> wf f -> typ f t T.
simple induction 1; intros.

auto with coc core arith datatypes.

auto with coc core arith datatypes.

elim red_item with n T0 e0 f; auto with coc core arith datatypes; intros.
inversion_clear H4.
inversion_clear H6.
elim H1; intros.
elim item_trunc with term n e0 x0; intros; auto with coc core arith datatypes.
elim wf_sort with n e0 x1 x0; auto with coc core arith datatypes.
intros.
apply type_conv with x x2; auto with coc core arith datatypes.
rewrite H6.
replace (Srt x2) with (lift (S n) (Srt x2));
 auto with coc core arith datatypes.
apply thinning_n with x1; auto with coc core arith datatypes.

apply coerce_conv.


elim item_trunc with term n e x0; intros; auto with coc core arith datatypes.
pose (wf_sort).
elim wf_sort with n e f x0; auto with coc core arith datatypes.
intros.

inversion_clear H4.
inversion_clear H2.
destruct H1; intros.
elim item_trunc with term n e0 x0; intros; auto with coc core arith datatypes.
elim wf_sort with n e0 x1 x0; auto with coc core arith datatypes.
intros.
apply type_conv with (lift 1 x) x2; auto with coc core arith datatypes.

apply type_var ; auto.
rewrite 
exists x ; auto.
apply item_hd.

rewrite H1.
replace (Srt x2) with (lift (S n) (Srt x2));
 auto with coc core arith datatypes.
apply thinning_n with x1; auto with coc core arith datatypes.
rewrite H7 ; auto with coc core arith datatypes.


cut (wf (T0 :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

apply type_pair with s1 s2; auto with coc core arith datatypes.
apply H5 ; auto with coc.
apply wf_var with s1 ; auto with coc core.

cut (wf (T0 :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with V ; auto with coc core arith datatypes.

apply type_pi2 with U ; auto with coc core arith datatypes.

cut (wf (U :: f)); intros.
apply type_let_in with U s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.

apply type_conv with U s; auto with coc core arith datatypes.
Qed.

  Inductive red1_exp_in_env : env -> env -> Prop :=
    | red1_exp_env_hd : forall e t u, red1 t u -> red1_exp_in_env (u :: e) (t :: e)
    | red1_exp_env_tl :
        forall e f t, red1_exp_in_env e f -> red1_exp_in_env (t :: e) (t :: f).

  Hint Resolve red1_exp_env_hd red1_exp_env_tl: coc.

  Lemma exp_item :
   forall n t e,
   item_lift t e n ->
   forall f,
   red1_exp_in_env e f ->
   item_lift t f n \/
   (forall g, trunc _ (S n) e g -> trunc _ (S n) f g) /\
   ex2 (fun u => red1 u t) (fun u => item_lift u f n).
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

exists (lift 1 t0) ;
unfold lift in |- *; auto with coc core arith datatypes.

exists t0; auto with coc core arith datatypes.

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
elim H5; auto with coc core arith datatypes.

right.
elim H2.
simple induction 2; intros.
split; intros.
inversion_clear H9; auto with coc core arith datatypes.

elim H8; intros.
exists (lift (S (S n0)) x1).
rewrite simpl_lift.
pattern (lift (S (S n0)) x) in |- *.
rewrite simpl_lift.
rewrite H9 in H7.
unfold lift.
apply red1_lift.
assumption.

exists x1; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.
Qed.

  Lemma typ_exp_env :
   forall e t T, typ e t T -> forall f, red1_exp_in_env e f -> wf f -> typ f t T.
simple induction 1; intros.
auto with coc core arith datatypes.

auto with coc core arith datatypes.

elim exp_item with v t0 e0 f; auto with coc core arith datatypes; intros.
inversion_clear H4.
inversion_clear H6.
elim H1; intros.
elim item_trunc with term v e0 x0; intros; auto with coc core arith datatypes.
elim wf_sort with v e0 x1 x0; auto with coc core arith datatypes.
intros.
apply type_conv with x x2; auto with coc core arith datatypes.
rewrite H6.
replace (Srt x2) with (lift (S v) (Srt x2));
 auto with coc core arith datatypes.
apply thinning_n with x1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

apply type_pair with s1 s2; auto with coc core arith datatypes.
apply H5 ; auto with coc.
apply wf_var with s1 ; auto with coc core.

cut (wf (T0 :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with V ; auto with coc core arith datatypes.

apply type_pi2 with U ; auto with coc core arith datatypes.

cut (wf (U :: f)); intros.
apply type_let_in with U s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.

apply type_conv with U s; auto with coc core arith datatypes.
Qed.



  Lemma subj_red : forall e t T, typ e t T -> forall u, red1 t u -> typ e u T.
induction 1; intros.
inversion_clear H0.

inversion_clear H0.

inversion_clear H1.

inversion_clear H2.
cut (wf (M' :: e)); intros.
apply type_conv with (Prod M' U) s2; auto with coc core arith datatypes.
apply type_abs with s1 s2; auto with coc core arith datatypes.
apply typ_red_env with (T :: e); auto with coc core arith datatypes.

apply typ_red_env with (T :: e); auto with coc core arith datatypes.

apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

apply type_abs with s1 s2; auto with coc core arith datatypes.

elim type_case with e u (Prod V Ur); intros;
 auto with coc core arith datatypes.
inversion_clear H2.
apply inv_typ_prod with e V Ur (Srt x); intros;
 auto with coc core arith datatypes.
generalize H H0. clear H H0.
inversion_clear H1; intros.
apply inv_typ_abs with e T M (Prod V Ur); intros;
 auto with coc core arith datatypes.
apply type_conv with (subst v T0) s2; auto with coc core arith datatypes.
apply substitution with T; auto with coc core arith datatypes.
apply type_conv with V s0; auto with coc core arith datatypes.
apply inv_conv_prod_l with Ur T0; auto with coc core arith datatypes.

unfold subst in |- *.
apply conv_conv_subst; auto with coc core arith datatypes.
apply inv_conv_prod_r with T V; auto with coc core arith datatypes.

replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

apply type_conv with (subst N2 Ur) s2; auto with coc core arith datatypes.
apply type_app with V; auto with coc core arith datatypes.

unfold subst in |- *.
apply conv_conv_subst; auto with coc core arith datatypes.

replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

discriminate.

inversion_clear H3.

inversion H4.
apply type_conv with (Sum N1 V) s2 ; auto with coc.
apply type_pair with s1 s2 ; auto with coc core.
apply type_conv with U s1 ; auto with coc core.
apply typ_red_env with (U :: e); auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.
apply type_sum with s1 ; auto with coc.
apply type_conv with (Sum U N2) s2 ; auto with coc.
apply type_pair with s1 s2 ; auto with coc core.
apply type_conv with (subst u V) s2 ; auto with coc core.
unfold subst ; apply conv_conv_subst ; auto with coc core.
replace (Srt s2) with (subst u (Srt s2)).
apply substitution with U ; auto with coc core arith datatypes.
unfold subst ; auto.
apply type_sum with s1 ; auto with coc.

apply type_pair with s1 s2 ; auto with coc core.
apply type_conv with (subst u V) s2 ; auto with coc core.
unfold subst ; apply conv_conv_subst ; auto with coc core.
replace (Srt s2) with (subst N1 (Srt s2)).
apply substitution with U ; auto with coc core arith datatypes.
unfold subst ; auto.

apply type_pair with s1 s2 ; auto with coc core.

inversion_clear H1.
apply type_prod with s1; auto with coc core arith datatypes.
apply typ_red_env with (T :: e); auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

apply type_prod with s1; auto with coc core arith datatypes.

inversion H1.
apply type_sum with s1 ; auto with coc core.
apply typ_red_env with (T :: e)  ; auto with coc core.
apply wf_var with s1  ; auto with coc core.

apply type_sum with s1 ; auto with coc core.

inversion H1.
apply type_subset ; auto with coc core.
apply typ_red_env with (T :: e)  ; auto with coc core.
apply wf_var with set ; auto with coc core.

apply type_subset ; auto with coc core.

generalize H IHtyp ; clear H IHtyp.
inversion_clear H0 ; intros.
induction (type_case _ _ _ H).
induction H0.
apply inv_typ_sum with e U V (Srt x) ; auto ; intros.
apply inv_typ_pair with e T u N (Sum U V) ; auto with coc ; intros.
apply type_conv with U0 s1 ; auto with coc core.
pose (inv_conv_sum_l _ _ _ _ H9).
apply sym_conv ; auto.
discriminate.

pose (IHtyp _ H).
apply type_pi1 with V ; auto.

generalize H IHtyp ; clear H IHtyp.
inversion_clear H0 ; intros.

inversion_clear H.
apply type_conv with (subst M V) s2; auto with coc core.
unfold subst ; apply conv_conv_subst ; auto with coc core.
replace (Srt s2) with (subst ((Pi1 (Pair (Sum U V) M u))) (Srt s2)).
apply substitution with U ; auto with coc core arith datatypes.
apply type_pi1 with V  ; auto with coc core arith datatypes.
apply type_pair with s1 s2 ; auto with coc.
unfold subst ; simpl ; auto.

induction (type_pair_unique2 _ _ _ H0 T M u (refl_equal (Pair T M u))).
induction H.
induction H.
assert (conv (Sum U V) (Sum x x0)).
apply trans_conv_conv with U0; auto with coc.
apply type_conv with (subst M V) s ; auto with coc core.
rewrite H in H0.
apply inv_typ_pair with e (Sum x x0) M u U0 ; auto with coc core ; intros.
apply inv_typ_sum with e U V (Srt s) ; auto with coc core arith ; intros.
apply type_conv with (subst M V0) s3 ; auto with coc core.
unfold subst ; apply conv_conv_subst ; auto with coc core arith.
assert(conv (Sum U V) (Sum U1 V0)).
apply trans_conv_conv with U0 ; auto with coc core.
apply inv_conv_sum_r with U1 U ; auto with coc core.
replace (Srt s3) with (subst M (Srt s3)) ;
[ apply substitution with U ; auto with coc core | unfold subst ; simpl ; auto  ].
apply type_conv with U1 s0 ; auto with coc core.
assert(conv (Sum U V) (Sum U1 V0)).
apply trans_conv_conv with U0 ; auto with coc core.
apply inv_conv_sum_l with V0 V ; auto with coc core.

unfold subst ; apply conv_conv_subst ; auto with coc core arith.

replace (Srt s) with (subst (Pi1 (Pair T M u)) (Srt s)) ;
[ apply substitution with U | unfold subst ; simpl ; auto  ].
apply inv_typ_sum with e U V (Srt s) ; auto ; intros.
rewrite <- (conv_sort _ _ H7).
assumption.

apply type_pi1 with V.
apply type_conv with U0 s ; auto with coc core.

pose (IHtyp _ H).
induction (type_case _ _ _ t0).
induction H1.
apply type_conv with (subst (Pi1 N) V) x ; auto with coc core.
apply type_pi2 with U ; auto with coc core.
unfold subst ; apply conv_conv_subst ; auto with coc core.
apply inv_typ_sum with e U V (Srt x) ; auto ; intros.
rewrite <- (conv_sort _ _ H4).
replace (Srt s2) with (subst (Pi1 t) (Srt s2)) ;
[ apply substitution with U | unfold subst ; simpl ; auto  ].
assumption.
apply type_pi1 with V ; auto.
discriminate.

generalize H IHtyp1 H0 IHtyp2 H1 IHtyp3 H2 IHtyp4.
clear H IHtyp1 H0 IHtyp2 H1 IHtyp3 H2 IHtyp4.
inversion_clear H3 ; intros.

pose (IHtyp1 _ H).
apply type_conv with (subst N1 M) s2 ; auto with coc core.
apply type_let_in with U s1 s2 ; auto with coc core.
unfold subst ; apply conv_conv_subst ; auto with coc core arith.
replace (Srt s2) with (subst t (Srt s2)) ;
[apply substitution with U ; auto with coc core | unfold subst ; auto].

pose (IHtyp3 _ H).
apply type_let_in with U s1 s2 ; auto with coc core.

apply type_conv with U s; auto with coc core arith datatypes.
Qed.


  Theorem subject_reduction :
   forall e t u, red t u -> forall T, typ e t T -> typ e u T.
simple induction 1; intros; auto with coc core arith datatypes.
apply subj_red with P; intros; auto with coc core arith datatypes.
Qed.