Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.LiftSubst.
Require Export Lambda.MyList.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Definition env := list term.

Implicit Types e f g : env.

Definition item_lift t e n :=
ex2 (fun u => t = lift (S n) u) (fun u => item term u (e:list term) n).

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
