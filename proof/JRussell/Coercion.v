Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.JRussell.Types.
Require Import Lambda.JRussell.Basic.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Inductive coerce_in_env : env -> env -> Prop :=
  | coerce_env_hd : forall e t u s, e |-= t >> u : s -> e |-= u : Srt s -> 
	coerce_in_env (t :: e) (u :: e)
  | coerce_env_tl :
        forall e f t, coerce_in_env e f -> coerce_in_env (t :: e) (t :: f).

Hint Resolve coerce_env_hd coerce_env_tl: coc.

Lemma ind_coerce_env :
  (forall e t T, e |-= t : T -> 
  forall f, coerce_in_env e f -> f |-= t : T) /\
  (forall e T U s, e |-= T >> U : s -> 
  forall f, coerce_in_env e f -> f |-= T >> U : s) /\
  (forall e U V T, e |-= U = V : T ->
  forall f, coerce_in_env e f -> f |-= U = V : T).
Proof.
apply typ_coerce_jeq_ind with 
(P := fun e t T => fun H : typ e t T =>
  forall f, coerce_in_env e f -> 
  typ f t T)
(P0 := fun e T U s => fun H : e |-= T >> U : s =>
  forall f, coerce_in_env e f -> 
  f |-= T >> U : s) 
(P1 := fun e U V T => fun H : e |-= U = V : T =>
  forall f, coerce_in_env e f -> 
  f |-= U = V : T) ;
 intros ; try (solve [destruct (H f H0) ; clear H]); 
auto with coc core arith datatypes.

inversion H ; auto with coc.
inversion H ; auto with coc.

inversion H0.
apply type_conv with (lift 1 u) s0 ; auto with coc.
apply type_var with s0 ; auto with coc .
apply coerce_weak with s0 ; auto with coc.

apply type_var with s ; auto with coc.

inversion H1.
apply type_weak with s0 ; auto.
apply type_weak with s ; auto.

apply type_abs with s1 s2 ; auto with coc.

apply type_app with V ; auto with coc.

apply type_pair with s1 s2 s3 ; auto with coc.

apply type_prod with s1 ; auto with coc.

apply type_sum with s1 s2 ; auto with coc.

apply type_subset ; auto with coc.

apply type_pi1 with V ; auto with coc.

apply type_pi2 with U ; auto with coc.

apply type_conv with U s ; auto with coc.

inversion H1.
apply coerce_weak with s0 ; auto with coc.
apply coerce_weak with s' ; auto with coc.

apply coerce_prod with s ; auto with coc.

apply coerce_sum with s s' ; auto with coc.

apply coerce_trans with B ; auto with coc.

inversion H1.
apply jeq_weak with s0 ; auto with coc.
apply jeq_weak with s ; auto with coc.

apply jeq_prod with s1 ; auto with coc.

apply jeq_abs with s1 s2 ; auto with coc.

apply jeq_app with A ; auto with coc.

apply jeq_beta with s1 s2 ; auto with coc.

apply jeq_sum with s1 s2 ; auto with coc.

apply jeq_pair with s1 s2 s3; auto with coc.

apply jeq_pi1 with B; auto with coc.

apply jeq_pi1_red with s1 s2 s3; auto with coc.

apply jeq_pi2 with A ; auto with coc.

apply jeq_pi2_red with s1 s2 s3; auto with coc.

apply jeq_subset ; auto with coc.

apply jeq_trans with N ; auto with coc.

apply jeq_conv with A s ; auto with coc.
Qed.

Lemma typ_coerce_env : forall e t T, e |-= t : T -> forall f, coerce_in_env e f -> 
  f |-= t : T.
Proof (proj1 ind_coerce_env).

Lemma coerce_coerce_env : forall e T U s, e |-= T >> U : s -> 
  forall f, coerce_in_env e f -> 
  f |-= T >> U : s.
Proof (proj1 (proj2 ind_coerce_env)).

Lemma jeq_coerce_env : forall e U V T, e |-= U = V : T -> 
  forall f, coerce_in_env e f -> 
  f |-= U = V : T.
Proof (proj2 (proj2 ind_coerce_env)).


