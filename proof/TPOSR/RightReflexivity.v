Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.CtxReduction.
Require Import Lambda.TPOSR.Substitution.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Lemma sub : forall g t u s, g |-- t ~= u : s -> t = u ->
  forall e d d' T, g = T :: e -> e |-- d -> d' : T ->
  e |-- lsubst d t ~= lsubst d' u : s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  apply tposr_eq_tposr.

Lemma ind_right_refl : 
  (forall e u v T, e |-- u -> v : T -> e |-- v -> v : T) /\
  (forall e, tposr_wf e -> True) /\
  (forall e u v s, e |-- u ~= v : s -> 
  e |-- u -> u : s /\ e |-- v -> v : s) /\
  (forall e u v s, e |-- u >-> v : s ->
  e |-- u -> u : s /\ e |-- v -> v : s).
Proof.
  apply ind_tposr_wf_eq_coerce with 
  (P:=fun e u v T => fun H : e |-- u -> v : T => e |-- v -> v : T) 
  (P0:=fun e => fun H : tposr_wf e => True) 
  (P1:=fun e u v s => fun H : e |-- u ~= v : s => 
  e |-- u -> u : s /\ e |-- v -> v : s)
  (P2:=fun e u v s => fun H : e |-- u >-> v : s =>
  e |-- u -> u : s /\ e |-- v -> v : s) ; simpl ; intros ; intuition ; auto with coc.

  assert(red_in_env (A :: e) (A' :: e)) by eauto with coc.
  apply tposr_prod with s1 ; eauto with coc ecoc.

  assert(red_in_env (A :: e) (A' :: e)) by eauto with coc.
  apply tposr_conv with (Prod_l A' B) s2 ; auto with coc.
  apply tposr_abs with s1 B s2 ; eauto with coc ecoc.
  apply tposr_coerce_prod with s1 ; eauto with coc ecoc.

  apply tposr_conv with (lsubst N' B') s2 ; auto with coc.
  apply tposr_app with  A A  s1 s2 ; auto with coc ecoc.
  eauto with coc.
  apply tposr_conv with (Prod_l A B) s2 ; auto with coc.
  apply tposr_coerce_prod with s1 ; eauto with coc ecoc.
  

  apply tposr_app with A A s1 s2 ; auto with coc.
  apply tposr_abs with s1 B s2 ; auto with coc.
  
  apply tposr_conv with A s ; auto with coc.

  apply tposr_sum with s1 s2 ; auto with coc.

  apply tposr_pair with s1 s2 s3 ; auto with coc.

  apply tposr_pi1 with s1 s2 s3 ; eauto with coc ecoc.

  apply tposr_pi1 with s1 s2 s3 ; eauto with coc ecoc.

  apply tposr_pi2 with s1 s2 s3 ; eauto with coc ecoc.

  apply tposr_pi2 with s1 s2 s3 ; eauto with coc ecoc.

  apply tposr_prod with s ; auto with coc.

  apply tposr_prod with s ; auto with coc.

  apply tposr_sum with s s' ; auto with coc.

  apply tposr_sum with s s' ; auto with coc.
Qed.

Corollary refl_l : forall e u v T, e |-- u -> v : T -> e |-- u -> u : T.
Proof (proj1 (ind_left_refl)).

Corollary tposrp_refl_l : forall e A B T, tposrp e A B T -> e |-- A -> A : T.
Proof.
  induction 1 ; auto with coc.
  apply (refl_l H).
Qed.

Corollary eq_refl_l : forall e u v s, e |-- u ~= v : s -> e |-- u -> u : s.
Proof.
  pose (proj1 (proj2 (proj2 (ind_left_refl)))).
  intros.
  destruct (a _ _ _ _ H) ; auto.
Qed. 

Corollary eq_refl_r : forall e u v s, e |-- u ~= v : s -> e |-- v -> v : s.
Proof.
  pose (proj1 (proj2 (proj2 (ind_left_refl)))).
  intros.
  destruct (a _ _ _ _ H) ; auto.
Qed. 

Corollary coerce_refl_l : forall e u v s, e |-- u >-> v : s -> e |-- u -> u : s.
Proof.
  pose (proj2 (proj2 (proj2 (ind_left_refl)))).
  intros.
  destruct (a _ _ _ _ H) ; auto.
Qed. 

Corollary coerce_refl_r : forall e u v s, e |-- u >-> v : s -> e |-- v -> v : s.
Proof.
  pose (proj2 (proj2 (proj2 (ind_left_refl)))).
  intros.
  destruct (a _ _ _ _ H) ; auto.
Qed. 

Hint Resolve refl_l tposrp_refl_l eq_refl_l eq_refl_r coerce_refl_l coerce_refl_r : coc.

Lemma refl_r : forall e u v T, e |-- u -> v : T -> e |-- v -> v : T.
Admitted.

Corollary eq_refls : forall e u v s, e |-- u ~= v : s -> 
  e |-- u -> u : Srt_l s /\ e |-- v -> v : Srt_l s.
Admitted.

Corollary coerce_refls : forall e u v s, e |-- u >-> v : s -> 
  e |-- u -> u : Srt_l s /\ e |-- v -> v : Srt_l s.
Admitted.

Corollary eq_refl_l :  forall e u v s, e |-- u ~= v : s -> e |-- u -> u : Srt_l s.
Proof.
  intros.
  apply (proj1 (eq_refls H)).
Qed.

Corollary eq_refl_r :  forall e u v s, e |-- u ~= v : s -> e |-- v -> v : Srt_l s.
Proof.
  intros.
  apply (proj2 (eq_refls H)).
Qed.

Corollary coerce_refl_l :  forall e u v s, e |-- u >-> v : s -> e |-- u -> u : Srt_l s.
Proof.
  intros.
  apply (proj1 (coerce_refls H)).
Qed.

Corollary coerce_refl_r :  forall e u v s, e |-- u >-> v : s -> e |-- v -> v : Srt_l s.
Proof.
  intros.
  apply (proj2 (coerce_refls H)).
Qed.

Lemma tposrp_refl_r : forall e A B T, tposrp e A B T -> e |-- B -> B : T.
Proof.
  induction 1 ; auto with coc.
  apply (refl_r H).
Qed.

Hint Resolve refl_r eq_refl_l eq_refl_r tposrp_refl_r : ecoc.
Hint Resolve coerce_refl_r coerce_refl_l tposrp_refl_r : ecoc.

