Require Import Termes.
Require Import Reduction.
Require Import LiftSubst.
Require Import CCSum.Types.
Require Import CCSum.Inversion.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

  Inductive ins_in_env A : nat -> env -> env -> Prop :=
    | ins_O : forall e, ins_in_env A 0 e (A :: e)
    | ins_S :
        forall n e f t,
        ins_in_env A n e f ->
        ins_in_env A (S n) (t :: e) (lift_rec 1 t n :: f).

  Hint Resolve ins_O ins_S: coc.

  Lemma ins_item_ge :
   forall A n e f,
   ins_in_env A n e f ->
   forall v : nat, n <= v -> forall t, item _ t e v -> item _ t f (S v).
simple induction 1; auto with coc core arith datatypes.
simple destruct v; intros.
inversion_clear H2.

inversion_clear H3; auto with coc core arith datatypes.
Qed.

  Lemma ins_item_lt :
   forall A n e f,
   ins_in_env A n e f ->
   forall v : nat,
   n > v -> forall t, item_lift t e v -> item_lift (lift_rec 1 t n) f v.
simple induction 1.
intros.
inversion_clear H0.

simple destruct v; intros.
elim H3; intros.
rewrite H4.
exists (lift_rec 1 t n0); auto with coc core arith datatypes.
inversion_clear H5.
elim permute_lift with t n0; auto with coc core arith datatypes.

elim H3; intros.
rewrite H4.
inversion_clear H5.
elim H1 with n1 (lift (S n1) x); intros; auto with coc core arith datatypes.
exists x0; auto with coc core arith datatypes.
pattern (lift (S (S n1)) x0) at 1 in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
elim H5.
change
  (lift_rec 1 (lift (S (S n1)) x) (S n0) =
   lift 1 (lift_rec 1 (lift (S n1) x) n0)) in |- *.
rewrite (permute_lift (lift (S n1) x) n0).
unfold lift at 2 in |- *.
pattern (lift (S (S n1)) x) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.
Qed.


  Lemma typ_weak_weak :
   forall A e t T,
   typ e t T ->
   forall n f,
   ins_in_env A n e f -> wf f -> typ f (lift_rec 1 t n) (lift_rec 1 T n).
simple induction 1; simpl in |- *; intros; auto with coc core arith datatypes.
elim (le_gt_dec n v); intros; apply type_var;
 auto with coc core arith datatypes.
elim H1; intros.
exists x.
rewrite H4.
unfold lift in |- *.
rewrite simpl_lift_rec; simpl in |- *; auto with coc core arith datatypes.

apply ins_item_ge with A n e0; auto with coc core arith datatypes.

apply ins_item_lt with A e0; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T0 n :: f)).
intro.
apply type_abs with s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

rewrite distr_lift_subst.
apply type_app with (lift_rec 1 V n); auto with coc core arith datatypes.

apply type_pair with s1 s2 ; auto with coc core arith datatypes.
apply H5 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

rewrite <- distr_lift_subst.
apply H7 ; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T0 n :: f)).
intro.
apply type_prod with s1; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.


cut (wf (lift_rec 1 T0 n :: f)).
intro.
apply type_sum with s1; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T0 n :: f)).
intro.
apply type_subset ; auto with coc core arith datatypes.
apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with (lift_rec 1 V (S n)) ; auto with coc.

rewrite distr_lift_subst.
simpl.
apply type_pi2 with (lift_rec 1 U n); auto with coc.

cut (wf (lift_rec 1 U n :: f)).
intro.
rewrite distr_lift_subst.
apply type_let_in with (lift_rec 1 U n) s1 s2 ; auto with coc core.
apply wf_var with s1 ; auto with coc core.

apply type_conv with (lift_rec 1 U n) s; auto with coc core arith datatypes.
Qed.


  Theorem thinning :
   forall e t T,
   typ e t T -> forall A, wf (A :: e) -> typ (A :: e) (lift 1 t) (lift 1 T).
unfold lift in |- *.
intros.
inversion_clear H0.
apply typ_weak_weak with A e; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.
Qed.


  Lemma thinning_n :
   forall n e f,
   trunc _ n e f ->
   forall t T, typ f t T -> wf e -> typ e (lift n t) (lift n T).
simple induction n.
intros.
rewrite lift0.
rewrite lift0.
replace e with f; auto with coc core arith datatypes.
inversion_clear H; auto with coc core arith datatypes.

do 8 intro.
inversion_clear H0.
intro.
rewrite simpl_lift; auto with coc core arith datatypes.
pattern (lift (S n0) T) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
inversion_clear H0.
change (typ (x :: e0) (lift 1 (lift n0 t)) (lift 1 (lift n0 T))) in |- *.
apply thinning; auto with coc core arith datatypes.
apply H with f; auto with coc core arith datatypes.
apply typ_wf with x (Srt s); auto with coc core arith datatypes.

apply wf_var with s; auto with coc core arith datatypes.
Qed.
