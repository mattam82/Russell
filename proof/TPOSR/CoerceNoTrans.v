Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.

Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Thinning.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.CtxCoercion.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Reserved Notation "G |-- T >>> U : s" (at level 70, T, U, s at next level).

Inductive coerces : lenv -> lterm -> lterm -> sort -> Set :=
  | coerces_refl : forall e A s, e |-- A -> A : s -> e |-- A >>> A : s

  | coerces_prod : forall e A B A' B',
  forall s, e |-- A' >>> A : s ->
  (* derivable *) e |-- A' -> A' : s -> e |-- A -> A : s ->
  forall s', (A' :: e) |-- B >>> B' : s' ->
  (* derivable *) A :: e |-- B -> B : s' -> A' :: e |-- B' -> B' : s' ->
  e |-- (Prod_l A B) >>> (Prod_l A' B') : s'

  | coerces_sum : forall e A B A' B',
  forall s, e |-- A >>> A' : s ->
  (* derivable *) e |-- A' -> A' : s -> e |-- A -> A : s ->
  forall s', (A :: e) |-- B >>> B' : s' ->
  (* derivable *) A :: e |-- B -> B : s' -> A' :: e |-- B' -> B' : s' ->
  forall s'', sum_sort s s' s'' -> 
  e |-- (Sum_l A B) >>> (Sum_l A' B') : s''

  | coerces_sub_l : forall e U P U',
  e |-- U >>> U' : set ->
  (* derivable *) U :: e |-- P -> P : prop ->
  e |-- Subset_l U P >>> U' : set

  | coerces_sub_r : forall e U U' P,
  e |-- U >>> U' : set ->
  (* derivable *) U' :: e |-- P -> P : prop ->
  e |-- U >>> (Subset_l U' P) : set

  | coerces_conv_l : forall e A B C s,
  e |-- A -> A : s -> e |-- B -> B : s -> e |-- C -> C : s ->
  e |-- A ~= B : s -> e |-- B >>> C : s -> e |-- A >>> C : s

 | coerces_conv_r : forall e A B C s,
  e |-- A -> A : s -> e |-- B -> B : s -> e |-- C -> C : s ->
  e |-- A >>> B : s -> e |-- B ~= C : s -> e |-- A >>> C : s

where "G |-- T >>> U : s" := (coerces G T U s).

Hint Resolve coerces_refl coerces_prod coerces_sum coerces_sub_l coerces_sub_r : coc.
Hint Resolve coerces_conv_l coerces_conv_r : coc.

Scheme coerces_dep := Induction for coerces Sort Type.

Require Import Coq.Arith.Max.
Fixpoint depth (e : lenv) (T U : lterm) (s : sort) (d : e |-- T >>> U : s) {struct d}: nat :=
  match d with
  | coerces_refl e A s As => 0
  | coerces_prod e A B A' B' s HsubA A's As s' HsubBB' Bs B's =>
    S (max (depth HsubA) (depth HsubBB'))
  | coerces_sum e A B A' B' s HsubA A's As s' HsubBB' Bs B's s'' sum =>
    S (max (depth HsubA) (depth HsubBB'))
  | coerces_sub_l e U P U' HsubU Ps => S (depth HsubU)
  | coerces_sub_r e U U' P HsubU Ps => S (depth HsubU)
  | coerces_conv_l e A B C s As Bs Cs convAB HsubBC => S (depth HsubBC)
  | coerces_conv_r e A B C s As Bs Cs HsubAB convBC => S (depth HsubAB)

  end.

Require Import Lambda.TPOSR.CoerceDepth.

Lemma coerces_coerce_rc_depth : forall G T U s, forall d : G |-- T >>> U : s,
  G |-- T >-> U : s [depth d].
Proof.
  induction d ; intros ; auto with coc core.
  
  simpl ; apply coerce_rc_depth_prod with s ; auto.

  simpl ; apply coerce_rc_depth_sum with s s' ; auto.

  simpl ; auto with coc.

  simpl ; auto with coc.

  simpl ; apply coerce_rc_depth_conv_l with B ; auto with coc.

  simpl ; apply coerce_rc_depth_conv_r with B ; auto with coc.
Qed.

Theorem coerce_rc_depth_coerces : forall e T U s n, e |-- T >-> U : s [n] -> 
  exists d : (e |-- T >>> U : s), depth d = n.
Proof.
  intros.
  induction H.
  
  exists (coerces_refl H).
  simpl ; auto.

  destruct IHcoerce_rc_depth1.
  destruct IHcoerce_rc_depth2.
  exists (coerces_prod x H0 H1 x0 H3 H4).
  simpl ; auto.

  destruct IHcoerce_rc_depth1.
  destruct IHcoerce_rc_depth2.
  exists (coerces_sum x H0 H1 x0 H3 H4 H5).
  simpl ; auto.

  destruct IHcoerce_rc_depth.
  exists (coerces_sub_l x H0).
  simpl ; auto.

  destruct IHcoerce_rc_depth.
  exists (coerces_sub_r x H0).
  simpl ; auto.

  destruct IHcoerce_rc_depth.
  exists (coerces_conv_l H H0 H1 H2 x).
  simpl ; auto.

  destruct IHcoerce_rc_depth.
  exists (coerces_conv_r H H0 H1 x H3).
  simpl ; auto.
Qed.

Inductive coerces_in_env : lenv -> lenv -> Prop :=
  | coerces_env_hd : forall e t u s, e |-- t >>> u : s -> 
	coerces_in_env (u :: e) (t :: e)
  | coerces_env_tl :
        forall e f t, tposr_wf (t :: f) -> coerces_in_env e f -> coerces_in_env (t :: e) (t :: f).

Hint Resolve coerces_env_hd coerces_env_tl : ecoc.

Require Import Lambda.TPOSR.CtxCoercion.

Lemma coerces_coerce : forall e t u s, e |-- t >>> u : s -> e |-- t >-> u : s.
Proof.
  intros.
  pose (coerces_coerce_rc_depth H).
  apply (coerce_rc_depth_coerce c).
Qed.

Lemma coerces_in_env_coerce_in_env : forall e f, coerces_in_env e f -> coerce_in_env e f.
Proof.
  induction 1 ; intros ; eauto with coc.
  apply coerce_env_hd with s.
  apply coerces_coerce ; auto.
Qed.

Hint Resolve coerces_in_env_coerce_in_env : coc.

Lemma tposr_coerces_env :
  forall e t T, forall d : (e |-- t -> t : T),
  forall f, coerces_in_env e f -> 
  tposr_wf f -> f |-- t -> t : T.
Proof.
  intros.
  pose (coerces_in_env_coerce_in_env H).
  apply tposr_coerce_env with e ; auto with coc.
Qed.

Lemma eq_coerces_env :
  forall e t u s, forall d : (e |-- t ~= u : s),
  forall f, coerces_in_env e f -> 
  tposr_wf f -> f |-- t ~= u : s.
Proof.
  intros.
  pose (coerces_in_env_coerce_in_env H).
  apply eq_coerce_env with e ; auto with coc.
Qed.

Lemma coerces_coerces_env :
  forall e T U s, forall d : (e |-- T >>> U : s), 
  forall f, coerces_in_env e f -> 
  tposr_wf f -> 
	{ d' : f |-- T >>> U : s | (depth d') = depth d }.
Proof.
  induction d ; simpl ; intros.

  pose(tposr_coerces_env t H H0).
  exists (coerces_refl t0).
  simpl ; auto.

  destruct (IHd1 f H H0).
  assert(tposr_wf (A' :: f)) by (apply wf_cons with s ; eauto with coc ecoc).
  assert(coerces_in_env (A' :: e) (A' :: f)).
  apply coerces_env_tl ; eauto with coc ecoc.
  destruct (IHd2 _ H2 H1).
  assert(tposr_wf (A :: f)) by (apply wf_cons with s ; eauto with coc ecoc).
  assert(coerces_in_env (A :: e) (A :: f)).
  apply coerces_env_tl ; eauto with coc ecoc.
  pose (tposr_coerces_env t H H0).
  pose (tposr_coerces_env t0 H H0).
  pose (tposr_coerces_env t1 H4 H3).
  pose (tposr_coerces_env t2 H2 H1).
  pose (coerces_prod x t3 t4 x0 t5 t6).
  exists c.
  simpl.
  auto.

  destruct (IHd1 f H H0).
  assert(tposr_wf (A' :: f)) by (apply wf_cons with s ; eauto with coc ecoc).
  assert(coerces_in_env (A' :: e) (A' :: f)).
  apply coerces_env_tl ; eauto with coc ecoc.
  assert(tposr_wf (A :: f)) by (apply wf_cons with s ; eauto with coc ecoc).
  assert(coerces_in_env (A :: e) (A :: f)).
  apply coerces_env_tl ; eauto with coc ecoc.
  destruct (IHd2 _ H4 H3).
  pose (tposr_coerces_env t H H0).
  pose (tposr_coerces_env t0 H H0).
  pose (tposr_coerces_env t1 H4 H3).
  pose (tposr_coerces_env t2 H2 H1).
  pose (coerces_sum x t3 t4 x0 t5 t6 s0).
  exists c.
  simpl.
  auto.

  destruct (IHd f H H0).
  assert(tposr_wf (U :: f)).
  apply wf_cons with set.
  pose (coerces_coerce x).
  eauto with coc.
  assert(coerces_in_env (U :: e) (U :: f)).
  apply coerces_env_tl ; eauto with coc ecoc.
  
  pose (tposr_coerces_env t H2 H1).
  pose (coerces_sub_l x t0).
  exists c ; simpl ; auto.

  destruct (IHd f H H0).
  assert(tposr_wf (U' :: f)).
  apply wf_cons with set.
  pose (coerces_coerce x).
  eauto with coc.
  assert(coerces_in_env (U' :: e) (U' :: f)).
  apply coerces_env_tl ; eauto with coc ecoc.
  
  pose (tposr_coerces_env t H2 H1).
  pose (coerces_sub_r x t0).
  exists c ; simpl ; auto.

  destruct (IHd _ H H0).
  pose (tposr_coerces_env t H H0).
  pose (tposr_coerces_env t0 H H0).
  pose (tposr_coerces_env t1 H H0).
  pose (eq_coerces_env t2 H H0).
  exists (coerces_conv_l t3 t4 t5 t6 x) ; simpl ; auto.

  destruct (IHd _ H H0).
  pose (tposr_coerces_env t H H0).
  pose (tposr_coerces_env t0 H H0).
  pose (tposr_coerces_env t1 H H0).
  pose (eq_coerces_env t2 H H0).
  exists (coerces_conv_r t3 t4 t5 x t6) ; simpl ; auto.
Qed.

Lemma coerces_sym : forall e A B s, forall d : e |-- A >>> B : s, 
  { d' : e |-- B >>> A : s | depth d' = depth d }. 
Proof.
  induction d ; simpl ; intros ; auto with coc.

  exists (coerces_refl t) ; simpl ; auto.

  destruct IHd1 ; destruct IHd2.
  pose (wf_tposr t1).
  assert(coerces_in_env (A' :: e) (A :: e)).
  apply coerces_env_hd with s ; eauto with coc ecoc.

  destruct (coerces_coerces_env x0 H t3).
  exists (coerces_prod x t0 t x1 t2 t1).
  simpl ; rewrite e2 ; auto.

  destruct IHd1 ; destruct IHd2.
  pose (wf_tposr t2).
  assert(coerces_in_env (A :: e) (A' :: e)).
  apply coerces_env_hd with s ; eauto with coc ecoc.

  destruct (coerces_coerces_env x0 H t3).
  exists (coerces_sum x t0 t x1 t2 t1 s0).
  simpl ; rewrite e2 ; auto.

  destruct IHd.
  exists (coerces_sub_r x t).
  simpl ;  auto.

  destruct IHd.
  exists (coerces_sub_l x t).
  simpl ;  auto.

  destruct IHd.
  exists (coerces_conv_r t1 t0 t x (tposr_eq_sym t2)).
  simpl ; auto.

  destruct IHd.
  exists (coerces_conv_l t1 t0 t (tposr_eq_sym t2) x).
  simpl ; auto.
Qed. 

Require Import Lambda.TPOSR.ChurchRosser.
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.CtxConversion.

Lemma inv_eq_prod_l : forall e U V U' V' s, 
  e |-- Prod_l U V ~= Prod_l U' V' : s -> forall s1, e |-- U -> U : s1 -> e |-- U ~= U' : s1.
Proof.
  intros.
  destruct (injectivity_of_pi H) ; destruct_exists.
  rewrite (unique_sort (eq_refl_l H1) H0) in H1.
  assumption.
Qed.

Lemma inv_eq_prod_r : forall e U V U' V' s, 
  e |-- Prod_l U V ~= Prod_l U' V' : s -> 
  U' :: e |-- V ~= V' : s.
Proof.
  intros.
  destruct (injectivity_of_pi H) ; destruct_exists.
  apply eq_conv_env with (U :: e) ; auto with coc.
  apply conv_env_hd with x ; auto with coc.
Qed.

Lemma inv_eq_sum_l : forall e U V U' V' s, 
  e |-- Sum_l U V ~= Sum_l U' V' : s -> 
  forall s1 : sort, e |-- U -> U : s1 -> e |-- U ~= U' : s1.
Proof.
  intros.
  destruct (injectivity_of_sum H) ; destruct_exists.
  rewrite (unique_sort (eq_refl_l H1) H0) in H1.
  assumption.
Qed.

Lemma inv_eq_sum_r : forall e U V U' V' s, 
  e |-- Sum_l U V ~= Sum_l U' V' : s -> 
  forall s2 : sort, U :: e |-- V -> V : s2 -> U :: e |-- V ~= V' : s2.
Proof.
  intros.
  destruct (injectivity_of_sum H) ; destruct_exists.
  rewrite (unique_sort (eq_refl_l H2) H0) in H2.
  assumption.
Qed.

Lemma inv_eq_subset_l_set : forall e U V U' V' s, 
  e |-- Subset_l U V ~= Subset_l U' V' : s -> e |-- U ~= U' : set.
Proof.
  intros.
  destruct (injectivity_of_subset H) ; destruct_exists.
  assumption.
Qed.
