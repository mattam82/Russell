Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.Russell.Types.
Require Import Lambda.Russell.Thinning.
Require Import Lambda.Russell.Substitution.
Require Import Lambda.Russell.Depth.


Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Reserved Notation "G |-- T >>>> U : s" (at level 70, T, U, s at next level).

Inductive coerces : env -> term -> term -> sort -> Set :=
  | coerce_refl : forall e A s, e |-- A : Srt s -> e |-- A >>>> A : s

  | coerce_prod : forall e A B A' B',
  forall s, e |-- A' >>>> A : s ->
  (* derivable *) e |-- A' : Srt s -> e |-- A : Srt s ->
  forall s', (A' :: e) |-- B >>>> B' : s' ->
  (* derivable *) A :: e |-- B : Srt s' -> A' :: e |-- B' : Srt s' ->
  e |-- (Prod A B) >>>> (Prod A' B') : s'

  | coerce_sum : forall e A B A' B',
  forall s, e |-- A >>>> A' : s ->
  (* derivable *) e |-- A' : Srt s -> e |-- A : Srt s ->
  forall s', (A :: e) |-- B >>>> B' : s' ->
  (* derivable *) A :: e |-- B : Srt s' -> A' :: e |-- B' : Srt s' ->
  forall s'', sum_sort s s' s'' -> sum_sort s s' s'' ->
  e |-- (Sum A B) >>>> (Sum A' B') : s''

  | coerce_sub_l : forall e U P U',
  e |-- U >>>> U' : set ->
  (* derivable *) U :: e |-- P : Srt prop ->
  e |-- Subset U P >>>> U' : set

  | coerce_sub_r : forall e U U' P,
  e |-- U >>>> U' : set ->
  (* derivable *) U' :: e |-- P : Srt prop ->
  e |-- U >>>> (Subset U' P) : set

  | coerce_conv : forall e A B C D s,
  e |-- A : Srt s -> e |-- B : Srt s -> e |-- C : Srt s -> e |-- D : Srt s ->
  conv A B -> e |-- B >>>> C : s -> conv C D -> e |-- A >>>> D : s

where "G |-- T >>>> U : s" := (coerces G T U s).

Hint Resolve coerce_refl coerce_prod coerce_sum coerce_sub_l coerce_sub_r : coc.
Hint Resolve coerce_conv : coc.



Reserved Notation "G |-- T >>> U : s" (at level 70, T, U, s at next level).

Inductive coerces_db : env -> term -> term -> sort -> Set :=
  | coerces_refl : forall e A s, e |-- A : Srt s -> e |-- A >>> A : s

  | coerces_prod : forall e A B A' B',
  forall s, e |-- A' >>> A : s ->
  (* derivable *) e |-- A' : Srt s -> e |-- A : Srt s ->
  forall s', (A' :: e) |-- B >>> B' : s' ->
  (* derivable *) A :: e |-- B : Srt s' -> A' :: e |-- B' : Srt s' ->
  e |-- (Prod A B) >>> (Prod A' B') : s'

  | coerces_sum : forall e A B A' B',
  forall s, e |-- A >>> A' : s ->
  (* derivable *) e |-- A' : Srt s -> e |-- A : Srt s ->
  forall s', (A :: e) |-- B >>> B' : s' ->
  (* derivable *) A :: e |-- B : Srt s' -> A' :: e |-- B' : Srt s' ->
  forall s'', sum_sort s s' s'' -> sum_sort s s' s'' ->
  e |-- (Sum A B) >>> (Sum A' B') : s''

  | coerces_sub_l : forall e U P U',
  e |-- U >>> U' : set ->
  (* derivable *) U :: e |-- P : Srt prop ->
  e |-- Subset U P >>> U' : set

  | coerces_sub_r : forall e U U' P,
  e |-- U >>> U' : set ->
  (* derivable *) U' :: e |-- P : Srt prop ->
  e |-- U >>> (Subset U' P) : set

  | coerces_conv_l : forall e A B C s,
  e |-- A : Srt s -> e |-- B : Srt s -> e |-- C : Srt s ->
  conv A B -> e |-- B >>> C : s -> e |-- A >>> C : s

  | coerces_conv_r : forall e A B C s,
  e |-- A : Srt s -> e |-- B : Srt s -> e |-- C : Srt s ->
  e |-- A >>> B : s -> conv B C -> e |-- A >>> C : s

where "G |-- T >>> U : s" := (coerces_db G T U s).

Hint Resolve coerces_refl coerces_prod coerces_sum coerces_sub_l coerces_sub_r : coc.
Hint Resolve coerces_conv_l coerces_conv_r : coc.

Scheme coerces_db_dep := Induction for coerces_db Sort Type.

Require Import Coq.Arith.Max.
Fixpoint depth (e : env) (T U : term) (s : sort) (d : e |-- T >>> U : s) {struct d}: nat :=
  match d with
  | coerces_refl e A s As => 0
  | coerces_prod e A B A' B' s HsubA A's As s' HsubBB' Bs B's =>
    S (max (depth HsubA) (depth HsubBB'))
  | coerces_sum e A B A' B' s HsubA A's As s' HsubBB' Bs B's s'' sum sum' =>
    S (max (depth HsubA) (depth HsubBB'))
  | coerces_sub_l e U P U' HsubU Ps => S (depth HsubU)
  | coerces_sub_r e U U' P HsubU Ps => S (depth HsubU)
  | coerces_conv_l e A B C s As Bs Cs convAB HsubBC => S (depth HsubBC)
  | coerces_conv_r e A B C s As Bs Cs HsubAB convBC => S (depth HsubAB)

  end.

Lemma coerces_coerces_db : forall G T U s, G |-- T >>>> U : s -> G |-- T >>> U : s.
Proof.
  induction 1 ; intros ; auto with coc core.

  apply coerces_prod with s; auto with coc.
  
  apply coerces_sum with s s'; auto with coc.

  apply coerces_conv_l with B ; auto with coc.
  apply coerces_conv_r with C ; auto with coc.
Qed.

Lemma coerces_db_coerces : forall G T U s, G |-- T >>> U : s -> G |-- T >>>> U : s.
Proof.
  induction 1 ; intros ; auto with coc core.

  apply coerce_prod with s; auto with coc.
  
  apply coerce_sum with s s'; auto with coc.

  apply coerce_conv with B C ; auto with coc.
  apply coerce_conv with A B ; auto with coc.
Qed.

Require Import Lambda.Russell.Coercion.

Inductive coerce_in_env : env -> env -> Prop :=
  | coerce_env_hd : forall e t u s, e |-- t >>> u : s -> 
	coerce_in_env (u :: e) (t :: e)
  | coerce_env_tl :
        forall e f t, wf (t :: f) -> coerce_in_env e f -> coerce_in_env (t :: e) (t :: f).

Hint Resolve coerce_env_hd coerce_env_tl: coc.


Theorem coerces_db_depth : forall e T U s n1, Depth.coerces_db e T U s n1 -> 
  exists d : (coerces_db e T U s), depth d = n1.
Proof.
  intros.
  induction H.
  
  exists (coerces_refl H).
  simpl ; auto.

  destruct IHcoerces_db1.
  destruct IHcoerces_db2.
  exists (coerces_prod x H0 H1 x0 H3 H4).
  simpl ; auto.

  destruct IHcoerces_db1.
  destruct IHcoerces_db2.
  exists (coerces_sum x H0 H1 x0 H3 H4 H5 H6).
  simpl ; auto.

  destruct IHcoerces_db.
  exists (coerces_sub_l x H0).
  simpl ; auto.

  destruct IHcoerces_db.
  exists (coerces_sub_r x H0).
  simpl ; auto.

  destruct IHcoerces_db.
  exists (coerces_conv_l H H0 H1 H2 x).
  simpl ; auto.

  destruct IHcoerces_db.
  exists (coerces_conv_r H H0 H1 x H3).
  simpl ; auto.
Qed.

Theorem depth_coerces_db : forall e T U s, coerces_db e T U s -> exists n, 
 Depth.coerces_db e T U s n.
Proof.
  induction 1 ; intros ; auto with coc core.
  exists 0 ; auto with coc.

  destruct IHcoerces_db1.
  destruct IHcoerces_db2.
  exists (S (max x x0)) ; simpl ; auto with coc.
  apply Depth.coerces_prod with s ; auto.

  destruct IHcoerces_db1.
  destruct IHcoerces_db2.
  exists (S (max x x0)) ; simpl ; auto with coc.
  apply Depth.coerces_sum with s s' ; auto.

  destruct IHcoerces_db.
  exists (S x) ; simpl ; auto with coc.

  destruct IHcoerces_db.
  exists (S x) ; simpl ; auto with coc.

  destruct IHcoerces_db.
  exists (S x) ; simpl ; auto with coc.
  apply Depth.coerces_conv_l with B ; auto with coc.

  destruct IHcoerces_db.
  exists (S x) ; simpl ; auto with coc.
  apply Depth.coerces_conv_r with B ; auto with coc.
Qed.

Lemma coerces_coerce : forall e T U s, e |-- T >>> U : s -> e |-- T >> U : s.
Proof.
  intros.
  destruct (depth_coerces_db H).
  apply (coerces_db_coerce H0).
Qed.

Lemma coerce_in_env_to_coercion : forall e f, coerce_in_env e f -> Coercion.coerce_in_env e f.
Proof.
  induction 1 ; simpl.
  destruct (depth_coerces_db H).
  pose (coerces_db_coerce H0).
  apply Coercion.coerce_env_hd with s ; auto.
  apply Coercion.coerce_env_tl ; auto.
Qed.  

Lemma coerce_in_env_from_coercion : forall e f, Coercion.coerce_in_env e f -> coerce_in_env e f.
Proof.
  induction 1 ; simpl.
  destruct (coerce_coerces_db H).
  destruct (coerces_db_depth H0).
  apply coerce_env_hd with s ; auto.
  apply coerce_env_tl ; auto.
Qed.  

Lemma typ_conv_env :
  forall e t T, forall d : (e |-- t : T),
  forall f, coerce_in_env e f -> 
  wf f -> f |-- t : T.
Proof.
  intros.
  pose (coerce_in_env_to_coercion H).
  apply typ_conv_env with e ; auto.
Qed.

Lemma coerce_conv_env :
  forall e T U s, forall d : (e |-- T >>> U : s), 
  forall f, coerce_in_env e f -> 
  wf f -> 
	{ d' : f |-- T >>> U : s | (depth d') = depth d }.
Proof.
  induction d ; simpl ; intros ; auto with coc.
  
  pose (typ_conv_env t H H0).
  exists (coerces_refl t0) ; simpl ; auto.

  pose (typ_conv_env t H H0).
  pose (typ_conv_env t0 H H0).
  destruct (IHd1 _ H H0).
  assert(wf (A' :: f)) by (apply wf_var with s ; eauto with coc).
  assert(coerce_in_env (A' :: e) (A' :: f)).
  apply coerce_env_tl ; eauto with coc.
  destruct (IHd2 _ H2 H1).
  assert(wf (A :: f)) by (apply wf_var with s ; eauto with coc).
  assert(coerce_in_env (A :: e) (A :: f)).
  apply coerce_env_tl ; eauto with coc.

  pose (typ_conv_env t1 H4 H3).
  pose (typ_conv_env t2 H2 H1).
  pose (coerces_prod x t3 t4 x0 t5 t6).
  exists c.
  simpl.
  auto.

  destruct (IHd1 f H H0).
  pose (typ_conv_env t H H0).
  pose (typ_conv_env t0 H H0).
  assert(wf (A' :: f)) by (apply wf_var with s ; eauto with coc).
  assert(coerce_in_env (A' :: e) (A' :: f)).
  apply coerce_env_tl ; eauto with coc.
  assert(wf (A :: f)) by (apply wf_var with s ; eauto with coc).
  assert(coerce_in_env (A :: e) (A :: f)).
  apply coerce_env_tl ; eauto with coc.
  destruct (IHd2 _ H4 H3).
  pose (typ_conv_env t1 H4 H3).
  pose (typ_conv_env t2 H2 H1).
  pose (coerces_sum x t3 t4 x0 t5 t6 s0 s1).
  exists c.
  simpl.
  auto.

  destruct (IHd f H H0).
  assert(wf (U :: f)).
  apply wf_var with set.
  pose (coerce_sort_l (coerces_coerce x)).
  eauto with coc.
  assert(coerce_in_env (U :: e) (U :: f)).
  apply coerce_env_tl ; eauto with coc.
  
  pose (typ_conv_env t H2 H1).
  pose (coerces_sub_l x t0).
  exists c ; simpl ; auto.

  destruct (IHd f H H0).
  assert(wf (U' :: f)).
  apply wf_var with set.
  pose (coerces_coerce x).
  eauto with coc.
  assert(coerce_in_env (U' :: e) (U' :: f)).
  apply coerce_env_tl ; eauto with coc.
  
  pose (typ_conv_env t H2 H1).
  pose (coerces_sub_r x t0).
  exists c ; simpl ; auto.

  destruct (IHd _ H H0).
  pose (typ_conv_env t H H0).
  pose (typ_conv_env t0 H H0).
  pose (typ_conv_env t1 H H0).
  exists (coerces_conv_l t2 t3 t4 c x) ; simpl ; auto.

  destruct (IHd _ H H0).
  pose (typ_conv_env t H H0).
  pose (typ_conv_env t0 H H0).
  pose (typ_conv_env t1 H H0).
  exists (coerces_conv_r t2 t3 t4 x c) ; simpl ; auto.
Qed.
