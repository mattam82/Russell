Require Import Termes.
Require Import Reduction.
Require Import LiftSubst.
Require Import CCSum.Types.
Require Import CCSum.Inversion.
Require Import CCSum.Thinning.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

  Lemma wf_sort_lift :
   forall n e t, wf e -> item_lift t e n -> exists s : sort, typ e t (Srt s).
simple induction n.
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



  Inductive sub_in_env t T : nat -> env -> env -> Prop :=
    | sub_O : forall e, sub_in_env t T 0 (T :: e) e
    | sub_S :
        forall e f n u,
        sub_in_env t T n e f ->
        sub_in_env t T (S n) (u :: e) (subst_rec t u n :: f).

  Hint Resolve sub_O sub_S: coc.

  Lemma nth_sub_sup :
   forall t T n e f,
   sub_in_env t T n e f ->
   forall v : nat, n <= v -> forall u, item _ u e (S v) -> item _ u f v.
simple induction 1.
intros.
inversion_clear H1; auto with coc core arith datatypes.

simple destruct v; intros.
inversion_clear H2.

inversion_clear H3; auto with coc core arith datatypes.
Qed.


  Lemma nth_sub_eq : forall t T n e f, sub_in_env t T n e f -> item _ T e n.
simple induction 1; auto with coc core arith datatypes.
Qed.


  Lemma nth_sub_inf :
   forall t T n e f,
   sub_in_env t T n e f ->
   forall v : nat,
   n > v -> forall u, item_lift u e v -> item_lift (subst_rec t u n) f v.
simple induction 1.
intros.
inversion_clear H0.

simple destruct v; intros.
elim H3; intros.
rewrite H4.
inversion_clear H5.
exists (subst_rec t u n0); auto with coc core arith datatypes.
apply commut_lift_subst; auto with coc core arith datatypes.

elim H3; intros.
rewrite H4.
inversion_clear H5.
elim H1 with n1 (lift (S n1) x); intros; auto with coc core arith datatypes.
exists x0; auto with coc core arith datatypes.
rewrite simpl_lift; auto with coc core arith datatypes.
pattern (lift (S (S n1)) x0) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
elim H5.
change
  (subst_rec t (lift 1 (lift (S n1) x)) (S n0) =
   lift 1 (subst_rec t (lift (S n1) x) n0)) in |- *.
apply commut_lift_subst; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.
Qed.


  Lemma typ_sub_weak :
   forall g (d : term) t,
   typ g d t ->
   forall e u (U : term),
   typ e u U ->
   forall f n,
   sub_in_env d t n e f ->
   wf f -> trunc _ n f g -> typ f (subst_rec d u n) (subst_rec d U n).
simple induction 2; simpl in |- *; intros; auto with coc core arith datatypes.
elim (lt_eq_lt_dec n v); [ intro Hlt_eq | intro Hlt ].
elim H2.
elim Hlt_eq; clear Hlt_eq.
case v; [ intro Hlt | intros n0 Hlt ]; intros.
inversion_clear Hlt.

simpl in |- *.
rewrite H6.
rewrite simpl_subst; auto with coc core arith datatypes.
apply type_var; auto with coc core arith datatypes.
exists x; auto with coc core arith datatypes.
apply nth_sub_sup with d t n e0; auto with coc core arith datatypes.

intro Heq; intros.
rewrite H6.
elim Heq.
rewrite simpl_subst; auto with coc core arith datatypes.
replace x with t.
apply thinning_n with g; auto with coc core arith datatypes.

apply fun_item with e0 v; auto with coc core arith datatypes.
apply nth_sub_eq with d f; auto with coc core arith datatypes.
elim Heq; auto with coc core arith datatypes.

apply type_var; auto with coc core arith datatypes.
apply nth_sub_inf with t e0; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

rewrite distr_subst.
apply type_app with (subst_rec d V n); auto with coc core arith datatypes.

apply type_pair with s1 s2 ; auto with coc core arith datatypes.
apply H6 ; auto with coc.
apply wf_var with s1 ; auto with coc.
rewrite <- distr_subst ; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with (subst_rec d V (S n)) ; auto with coc.

rewrite distr_subst.
simpl.
apply type_pi2 with (subst_rec d U0 n) ; auto with coc.

cut (wf (subst_rec d U0 n :: f)).
intro ; rewrite distr_subst.
apply type_let_in with (subst_rec d U0 n) s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

apply type_conv with (subst_rec d U0 n) s; auto with coc core arith datatypes.
Qed.

  Theorem substitution :
   forall e t u (U : term),
   typ (t :: e) u U ->
   forall d : term, typ e d t -> typ e (subst d u) (subst d U).
intros.
unfold subst in |- *.
apply typ_sub_weak with e t (t :: e); auto with coc core arith datatypes.
apply typ_wf with d t; auto with coc core arith datatypes.
Qed.
