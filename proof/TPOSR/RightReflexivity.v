Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.TypesNoDerivs.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.CtxReduction.
Require Import Lambda.TPOSR.CtxCoercion.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.SubstitutionTPOSR.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Lemma tposr_pair_red_left_aux : forall e t u T, e |-- t -> u : T ->
  forall A B a b, t = Pair_l (Sum_l A B) a b -> 
  u = t ->
  e |-- a -> a : A.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  pose (IHtposr  _ _ _ _ H1 H2).
  assumption.

  inversion H4 ; inversion H5.
  subst.
  assumption.
Qed. 

Lemma tposr_pair_red_left : forall e A B a b T, e |-- Pair_l (Sum_l A B) a b -> Pair_l (Sum_l A B) a b : T ->
  e |-- a -> a : A.
Proof.
  intros ; eapply tposr_pair_red_left_aux ; eauto with coc.
Qed.

Lemma tposr_pair_red_comp_aux : forall e t u T, e |-- t -> u : T ->
  forall A B a b, t = Pair_l (Sum_l A B) a b -> 
  forall A' B' a' b', u = Pair_l (Sum_l A' B') a' b' ->
  e |-- a -> a' : A /\ e |-- b -> b' : lsubst a B.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  pose (IHtposr  _ _ _ _ H1 _ _ _ _ H2).
  assumption.

  inversion H4 ; inversion H5.
  subst.
  intuition.
Qed. 

Lemma tposr_pair_red_comp : forall e A B a b A' B' a' b' T, e |-- Pair_l (Sum_l A B) a b -> Pair_l (Sum_l A' B') a' b' : T ->
  e |-- a -> a' : A /\ e |-- b -> b' : lsubst a B.
Proof.
  intros ; eapply tposr_pair_red_comp_aux ; eauto with coc.
Qed.

Lemma tposr_pair_coerce_left_aux : forall e t u T, e |-- t -> u : T ->
  forall A B a b, t = Pair_l (Sum_l A B) a b -> 
  forall A' B' a' b', u = Pair_l (Sum_l A' B') a' b' ->
  exists s : sort, e |-- A -> A' : s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  pose (IHtposr _ _ _ _ H1 _ _ _ _ H2).
  assumption.

  inversion H4 ; inversion H5.
  subst.
  exists s1.
  eauto with coc ecoc.
Qed. 

Lemma tposr_pair_coerce_left : forall e A B a b A' B' a' b' T, e |-- Pair_l (Sum_l A B) a b -> Pair_l (Sum_l A' B') a' b' : T ->
  exists s : sort, e |-- A -> A' : s.
Proof.
  intros ; eapply tposr_pair_coerce_left_aux ; eauto with coc.
Qed.

Lemma tposr_pair_red_right_aux : forall e t u T, e |-- t -> u : T ->
  forall A B a b, t = Pair_l (Sum_l A B) a b -> u = t ->
  e |-- b -> b : lsubst a B.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  pose (IHtposr _ _ _ _ H1 H2).
  assumption.

  inversion H4 ; inversion H5.
  subst.
  assumption.
Qed. 

Lemma tposr_pair_red_right : forall e A B a b T, e |-- Pair_l (Sum_l A B) a b -> Pair_l (Sum_l A B) a b : T ->
  e |-- b -> b : lsubst a B.
Proof.
  intros ; eapply tposr_pair_red_right_aux ; eauto with coc.
Qed.

Lemma tposr_pair_coerce_right_aux : forall e t u T, e |-- t -> u : T ->
  forall A B a b, t = Pair_l (Sum_l A B) a b -> 
  forall A' B' a' b', u = Pair_l (Sum_l A' B') a' b' ->
  exists s : sort, (A :: e) |-- B -> B' : s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  pose (IHtposr _ _ _ _ H1 _ _ _ _ H2).
  assumption.

  inversion H4 ; inversion H5.
  subst.
  exists s2.
  eauto with coc ecoc.
Qed. 

Lemma tposr_pair_coerce_right : forall e A B a b A' B' a' b' T, e |-- Pair_l (Sum_l A B) a b -> Pair_l (Sum_l A' B') a' b' : T ->
  exists s : sort, (A :: e) |-- B -> B' : s.
Proof.
  intros ; eapply tposr_pair_coerce_right_aux ; eauto with coc.
Qed.

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

  assert(red_in_env (A :: e) (A' :: e)) by eauto with coc ecoc.
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
  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with A ; auto with coc.
  apply tposr_conv with (lsubst N' B) s2 ; auto with coc.
  apply substitution_tposr_tposr with A ; auto with coc ecoc.
  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with A ; auto with coc.
  eauto with coc.
  
  apply tposr_conv with A s ; auto with coc.

  (* Subset *)
  assert(red_in_env (A :: e) (A' :: e)) by eauto with coc.
  apply tposr_subset ; eauto with coc ecoc.

  (* Sum *)
  assert(red_in_env (A :: e) (A' :: e)) by eauto with coc.
  apply tposr_sum with s1 s2 ; eauto with coc ecoc.

  (* Pair *)
  assert(red_in_env (A :: e) (A' :: e)) by eauto with coc.
  apply tposr_conv with (Sum_l A' B') s3 ; auto with coc.
  apply tposr_pair with s1 s2 s3 ; auto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_conv with A s1 ; eauto with coc ecoc.
 apply tposr_conv with (lsubst u B) s2 ; auto with coc.
 apply substitution_tposr_coerce with A ; eauto with coc ecoc.
 
  apply tposr_coerce_sum with s1 s2 ; auto with coc ecoc.
  eauto with coc.
  eauto with coc.
  apply coerce_red_env with (A :: e) ; auto with coc.
  eauto with coc.
  apply tposr_red_env with (A :: e) ; auto with coc.
  eauto with coc.

  (* Pi1_l *)
  apply tposr_conv with A' s1 ; auto with coc.
  assert(coerce_in_env (A :: e) (A' :: e)).
  apply coerce_env_hd with s1 ; auto with coc.
  apply tposr_pi1 with s1 s2 s3 ; auto with coc ecoc.
  apply coerce_coerce_env with (A :: e) ; auto with coc.
  apply tposr_conv with (Sum_l A B) s3 ; auto with coc.
  apply tposr_coerce_sum with s1 s2 ; auto with coc.
  apply tposr_coerce_env with (A :: e) ; auto with coc.
  apply tposr_conv with A' s1 ; auto with coc.
  pose (tposr_pair_red_left H2) .
  destruct (tposr_pair_coerce_left t2) .
  apply tposr_conv with A'' x ; eauto with coc.

  (* Pi2 *)
  assert(coerce_in_env (A :: e) (A' :: e)).
  apply coerce_env_hd with s1 ; auto with coc.

  apply tposr_conv with (lsubst (Pi1_l (Sum_l A' B') t') B') s2 ; auto with coc.  
  apply tposr_pi2 with s1 s2 s3 ; eauto with coc ecoc.
  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with A' ; eauto with coc.
  apply coerce_coerce_env with (A :: e) ; eauto with coc.
  apply tposr_pi1 with s1 s2 s3 ; auto with coc ecoc.
  apply coerce_coerce_env with (A :: e) ; auto with coc.
  apply tposr_conv with (Sum_l A B) s3 ; auto with coc.
  apply tposr_coerce_sum with s1 s2 ; auto with coc.
  apply tposr_coerce_env with (A :: e) ; auto with coc.

  assert(coerce_in_env (A :: e) (A' :: e)).
  apply coerce_env_hd with s1 ; auto with coc.

  apply tposr_conv with  (lsubst u B') s2 ; auto with coc. 
  pose (tposr_pair_red_right H2) .
  destruct (tposr_pair_coerce_right t2) .
  apply tposr_conv with (lsubst u' B'') x ; auto with coc.
  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with A' ; eauto with coc.
  destruct(tposr_pair_red_comp t2).
  assumption.
  destruct(tposr_pair_red_comp H2).
  destruct(tposr_pair_coerce_left t2).
  apply tposr_conv with A'' x0 ; eauto with coc.

  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with A ; eauto with coc.
  destruct (tposr_pair_red_comp t2).
  pose (refl_l H6).
  apply tposr_conv with A' s1 ; auto with coc.

  apply tposr_prod with s ; eauto with coc ecoc.

  apply tposr_prod with s ; eauto with coc ecoc.

  apply tposr_sum with s s' ; eauto with coc ecoc.

  apply tposr_sum with s s' ; eauto with coc ecoc.
Qed.

Corollary refl_r : forall e u v T, e |-- u -> v : T -> e |-- v -> v : T.
Proof (proj1 (ind_right_refl)).

Corollary tposrp_refl_r : forall e A B T, tposrp e A B T -> e |-- B -> B : T.
Proof.
  induction 1 ; auto with coc.
  apply (refl_r H).
Qed.

Corollary eq_refl_l : forall e u v s, e |-- u ~= v : s -> e |-- u -> u : s.
Proof.
  pose (proj1 (proj2 (proj2 (ind_right_refl)))).
  intros.
  destruct (a _ _ _ _ H) ; auto.
Qed. 

Corollary eq_refl_r : forall e u v s, e |-- u ~= v : s -> e |-- v -> v : s.
Proof.
  pose (proj1 (proj2 (proj2 (ind_right_refl)))).
  intros.
  destruct (a _ _ _ _ H) ; auto.
Qed. 

Corollary coerce_refl_l : forall e u v s, e |-- u >-> v : s -> e |-- u -> u : s.
Proof.
  pose (proj2 (proj2 (proj2 (ind_right_refl)))).
  intros.
  destruct (a _ _ _ _ H) ; auto.
Qed. 

Corollary coerce_refl_r : forall e u v s, e |-- u >-> v : s -> e |-- v -> v : s.
Proof.
  pose (proj2 (proj2 (proj2 (ind_right_refl)))).
  intros.
  destruct (a _ _ _ _ H) ; auto.
Qed. 

Hint Resolve refl_r tposrp_refl_r eq_refl_l eq_refl_r coerce_refl_l coerce_refl_r : coc.
