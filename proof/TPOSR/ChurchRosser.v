Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.MyList.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Basic.
Require Import Lambda.TPOSR.Thinning.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.CtxConversion.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.Equiv.
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.Validity.
Require Import Lambda.TPOSR.TypesDepth.
Require Import Lambda.TPOSR.TypesFunctionality.
Require Import Lambda.TPOSR.UniquenessOfTypes.
Require Import Lambda.TPOSR.ChurchRosserDepth.

Require Import Lambda.Meta.TPOSR_Russell.

Set Implicit Arguments.

Corollary church_rosser : forall G M N A, G |-- M -> N : A -> forall P B, G |-- M -> P : B ->
  exists Q, 
  (G |-- N -> Q : A /\
  G |-- N -> Q : B /\
  G |-- P -> Q : A /\
  G |-- P -> Q : B).
Proof.
  intros.
  pose (tod H).
  pose (tod H0).
  destruct_exists.
  apply (church_rosser_depth H2 H1).
Qed.

Inductive tposrp_n : lenv -> lterm -> lterm -> lterm -> nat -> Prop :=
  | tposrp_n_tposr : forall e X Y Z, e |-- X -> Y : Z -> tposrp_n e X Y Z 1
  | tposrp_n_trans : forall e W X Z, e |-- W -> X : Z -> forall Y m, tposrp_n e X Y Z m ->
  tposrp_n e W Y Z (S m).

Lemma tposrp_n_tposrp :  forall e T U s n, tposrp_n e T U s n -> tposrp e T U s.
Proof.
  induction 1.
  apply tposrp_tposr ; auto.
  apply tposrp_trans with X ; auto.
  apply tposrp_tposr ; auto.
Qed. 

Lemma tposrp_n_cr : 
  forall n m e A B T, tposrp_n e A B T n -> forall C, tposrp_n e A C T m -> 
  exists D, tposrp_n e B D T m /\ tposrp_n e C D T n.
Proof.
  intros n ; pattern n.
  apply wf_lt_induction_type.
  intros n' IH.
  intros m ; pattern m.
  apply wf_lt_induction_type.
  intros m' IH'.
  induction 1 ; simpl.
  induction 1 ; simpl.

  pose (church_rosser H H0) ; destruct_exists.
  exists x ; intuition.
  apply tposrp_n_tposr ; auto.
  apply tposrp_n_tposr ; auto.

  clear IHtposrp_n.  
  pose (church_rosser H H0); destruct_exists.
  assert(m0 < S m0) ; auto with arith.
  pose (tposrp_n_tposr H4).
  pose (IH' _ H6 _ _ _ _ t _ H1) ; destruct_exists.
  exists x0 ; intuition.
  apply tposrp_n_trans with x ; auto.
  
  clear IHtposrp_n.
  induction 1 ; simpl.
  pose (church_rosser H H1) ; destruct_exists.
  pose (tposrp_n_tposr H2).
  assert(m0 < S m0) ; auto with arith.
  pose (IH _ H6 1 _ _ _ _ H0 _ (tposrp_n_tposr H2)) ; destruct_exists.
  exists x0 ; intuition.
  apply tposrp_n_trans with x ; auto.

  clear IHtposrp_n.
  pose (church_rosser H H1) ; destruct_exists.
  assert(m0 < S m0) ; auto with arith.
  pose (IH _ H7 _ _ _ _ _ H0 _ (tposrp_n_tposr H3)) ; destruct_exists.
  assert(m1 < S m1) ; auto with arith.
  pose (tposrp_n_trans H6 H9).
  pose (IH' _ H10 _ _ _ _ t _ H2) ; destruct_exists.
  exists x1 ; intuition ; auto with coc.
  apply tposrp_n_trans with x0 ; auto.
  inversion H8.
  assumption.
  inversion_clear H19.
Qed.

Lemma tposrp_n_transitive : forall e T U s n, tposrp_n e T U s n -> forall V m, tposrp_n e U V s m ->
  tposrp_n e T V s (n + m).
Proof.
  induction 1 ; intros.
  simpl.
  apply tposrp_n_trans with Y ; auto.
  pose (IHtposrp_n V m0 H1).
  change (S m + m0) with (S (m + m0)).
  apply tposrp_n_trans with X ; auto with coc.
Qed.


Lemma tposrp_tposrp_n : forall e T U s, tposrp e T U s -> exists n, tposrp_n e T U s n.
Proof.
  induction 1.
  exists 1 ; apply tposrp_n_tposr ; auto.
  destruct_exists.
  exists (x0 + x).
  apply tposrp_n_transitive with X ; auto.
Qed. 

Corollary tposrp_cr : 
  forall e A B T, tposrp e A B T -> forall C, tposrp e A C T -> 
  exists D, tposrp e B D T /\ tposrp e C D T.
Proof.
  intros.
  pose (tposrp_tposrp_n H).
  pose (tposrp_tposrp_n H0).
  destruct_exists.
  pose (tposrp_n_cr H2 H1).
  destruct_exists.
  exists x1.
  split ; [apply tposrp_n_tposrp with x | apply tposrp_n_tposrp with x0] ; auto.
Qed.

Corollary tposr_eq_cr : forall e A B s, e |-- A ~= B : s -> 
  exists C, tposrp e A C (Srt_l s) /\ tposrp e B C (Srt_l s).
Proof.
  induction 1.
  pose (church_rosser H (left_refl H)) ; destruct_exists.
  exists x ; intuition ; auto with coc.

  destruct_exists.
  exists x ; intuition.

  destruct_exists.
  pose (tposrp_cr H4 H1) ; destruct_exists.
  exists x1 ; intuition.
  apply tposrp_trans with x0 ; auto with coc.
  apply tposrp_trans with x ; auto with coc.
Qed.

Lemma tposr_sort_aux : forall e T T' s', tposr e T T' s' -> forall s, T = Srt_l s -> T' = Srt_l s.
Proof.
  induction 1 ; intros ; try discriminate ; auto with coc.
Qed. 

Lemma tposr_sort : forall e s T' s', tposr e (Srt_l s) T' s' -> T' = Srt_l s.
Proof.
  intros ; apply tposr_sort_aux with e (Srt_l s) s' ; auto.
Qed. 
 
Lemma tposrp_sort_aux : forall e T T' s', tposrp e T T' s' -> forall s, T = Srt_l s -> T' = Srt_l s.
Proof.
  induction 1 ; intros.
  rewrite H0 in H.
  pose (generation_sort H).
  intuition.

  pose (IHtposrp1 _ H1).
  apply (IHtposrp2 _ e0).
Qed.

Lemma tposrp_sort : forall e s T' s', tposrp e (Srt_l s) T' s' -> T' = Srt_l s.
Proof.
  intros.
  apply (tposrp_sort_aux H) ; auto.
Qed.

Lemma tposr_eq_sort : forall e s s0 s', tposr_eq e (Srt_l s) (Srt_l s0) s' -> s = s0.
Proof.
   intros.
   pose (tposr_eq_cr H) ; destruct_exists.
   pose (tposrp_sort H0).
   pose (tposrp_sort H1).
   rewrite e0 in e1.
   inversion e1 ; auto.
Qed.  

Lemma inv_llift_sort : forall t s n, llift n t = Srt_l s -> t = Srt_l s.
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold llift in H ; simpl in H.
auto.
Qed.

Lemma inv_subst_sort : forall t t' n s, lsubst_rec t t' n = Srt_l s -> 
  t = Srt_l s \/ t' = Srt_l s.
Proof.
  induction t' ;  simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  generalize H.
  elim (lt_eq_lt_dec n0 n).
  intros a ; case a ; clear a ; intros ; try discriminate ; auto.
  left.
  exact (inv_llift_sort _ _ H0).

  intros.
  discriminate.
Qed.

Lemma tposr_sort_kinded : forall e T U, e |-- T -> T : U ->
  forall s, T = Srt_l s -> U = kind.
Proof.
  induction 1 ; simpl ; intros; try discriminate ; auto with coc.
  
  unfold lsubst in H3.
  destruct (inv_subst_sort _ _ _ H3).
  
  pose (IHtposr4 _ H4).
  rewrite e0 in H.
  elim (tposr_not_kind H).

  pose (IHtposr3 _ H4).
  rewrite e0 in H0.
  elim (tposr_not_kind H0).

  pose (IHtposr _ H1).
  rewrite e0 in H0.
  pose (coerce_refl_l H0).
  elim (tposr_not_kind t).

  pose (generation_pair H2) ; destruct_exists.
  inversion H12 ; subst.
  inversion H6 ; subst.
Admitted. 

Lemma in_set_not_sort : forall e T s, e |-- T -> T : s ->
  s = set -> forall s, T <> Srt_l s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  red ; intros.
  destruct (inv_subst_sort _ _ _ H3).
  rewrite H5 in H2.
  pose (tposr_sort_kinded (left_refl H2) (refl_equal (Srt_l set))).
  rewrite e0 in H.
  elim (tposr_not_kind H).
  pose (IHtposr3 H5).
  destruct (inv_subst_sort _ _ _ H4).
  rewrite H6 in H2.
  pose (tposr_sort_kinded (right_refl H2) (refl_equal (Srt_l s))).
  rewrite e0 in H.
  elim (tposr_not_kind H).
  pose (n s) ; contradiction.
  red ; intros.
  rewrite H2 in H.
  pose (tposr_sort_kinded (right_refl H) (refl_equal (Srt_l s0))).
  rewrite e0 in H0.
  elim (tposr_not_kind (coerce_refl_l H0)).

  rewrite H5 in H3.
  pose (tposr_sort_kinded (coerce_refl_l H3) (refl_equal (Srt_l set))).
  injection e0 ; intros.
  rewrite H6 in H1.
  destruct H1 ; intuition ; try discriminate.
  destruct (inv_subst_sort _ _ _ H5) ; try discriminate.
  rewrite H6 in H4.
  pose (tposr_sort_kinded (coerce_refl_l H4) (refl_equal (Srt_l set))).
  injection e0 ; intros.
  rewrite H7 in H1.
  destruct H1 ; intuition ; try discriminate.
Qed.

Lemma tposr_eq_sort_red : forall G T s s', G |-- T ~= (Srt_l s) : s' ->
  lred T (Srt_l s).
Proof.
  intros.
  pose (tposr_eq_cr H) ; destruct_exists.
  pose (tposrp_sort H1).
  rewrite e in H0.
  apply (tposrp_lred H0).
Qed.

Lemma tposr_coerce_sorts : forall e T U s', tposr_coerce e T U s' ->
  forall s, (e |-- T ~= (Srt_l s) : s' -> e |-- U ~= (Srt_l s) : s') /\
  (e |-- U ~= (Srt_l s) : s' -> e |-- T ~= (Srt_l s) : s').
Proof.
  induction 1 ; simpl ; split ; intros ; try discriminate.
  apply tposr_eq_trans with A ; auto with coc.
  apply tposr_eq_trans with B ; auto with coc.

  pose (tposr_eq_conv H5).
  elim conv_sort_prod with s0 A B ; auto with coc.
  pose (tposr_eq_conv H5).
  elim conv_sort_prod with s0 A' B' ; auto with coc.

  pose (tposr_eq_conv H7).
  elim conv_sort_sum with s0 A B ; auto with coc.
  pose (tposr_eq_conv H7).
  elim conv_sort_sum with s0 A' B' ; auto with coc.

  pose (tposr_eq_conv H3).
  elim conv_sort_subset with s U P ; auto with coc.
  pose (conv_refl_r H3).
  elim (in_set_not_sort t (refl_equal (Srt_l set))) with s.
  auto.
  pose (conv_refl_r H3).
  elim (in_set_not_sort t (refl_equal (Srt_l set))) with s.
  auto.
  pose (tposr_eq_conv H3).
  elim conv_sort_subset with s U' P ; auto with coc.

  destruct (IHtposr_coerce s0).
  apply (H2 H0).
  destruct (IHtposr_coerce s0).
  apply (H1 H0).

  destruct (IHtposr_coerce1 s0).
  pose (H2 H1).
  destruct (IHtposr_coerce2 s0).
  apply (H4 t).

  destruct (IHtposr_coerce1 s0).
  destruct (IHtposr_coerce2 s0).
  apply (H3 (H5 H1)).
Qed.

Lemma tposr_coerce_eq_sort_aux : forall e T U s', tposr_coerce e T U s' ->
  forall s s0, T = (Srt_l s) -> U = (Srt_l s0) -> s = s0.
Proof.
  intros.
  pose (tposr_coerce_sorts H).
  destruct (a s).
  rewrite H0 in H2.
  assert(e |-- s ~= s : s').
  rewrite H0 in H.
  pose (coerce_refl_l H4).
  auto with coc.
  pose (H2 H4).
  rewrite H1 in t.
  pose (tposr_eq_sort t).
  auto.
Qed.  

Lemma tposr_coerce_eq_sort : forall e s s0 s', e |-- (Srt_l s) >-> (Srt_l s0) : s' ->
  s = s0.
Proof.
  intros.
  eapply tposr_coerce_eq_sort_aux ; eauto with coc.
Qed.

Lemma equiv_eq_sort : forall e s s0, equiv e (Srt_l s) (Srt_l s0) -> s = s0.
Proof.
   intros.
   destruct H.
   destruct H ; destruct_exists.
   inversion H ; inversion H0 ; auto .

   destruct H.
   apply (tposr_coerce_eq_sort H).
Qed.  

Lemma tposrp_conv_env : forall e A B T, tposrp e A B T ->
  forall f, conv_in_env e f -> tposrp f A B T.
Proof.
  induction 1 ; intros ; auto with coc.
  apply tposrp_tposr.
  apply conv_env with e ; auto with coc.
  apply tposrp_trans with X ; auto with coc.
Qed.

Lemma tposrp_tposr_eq_aux : forall e A B T, tposrp e A B T -> forall s, T = Srt_l s -> e |-- A ~= B : s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  rewrite H0 in H.
  apply tposr_eq_tposr ; auto.
  apply tposr_eq_trans with X ; auto with coc.
Qed.

Lemma tposrp_tposr_eq : forall e A B s, tposrp e A B (Srt_l s) -> e |-- A ~= B : s.
Proof.
  intros ; apply tposrp_tposr_eq_aux with (Srt_l s) ; auto.
Qed.

Lemma tposrp_pi_aux : forall e T T' Ts, tposrp e T T' Ts -> 
  forall A B, T = Prod_l A B -> forall s, Ts  = Srt_l s -> exists3 A' B' s1, T' = Prod_l A' B' /\
  tposrp e A A' (Srt_l s1) /\ tposrp (A :: e) B B' (Srt_l s).
Proof.
  induction 1 ; simpl ; intros.
  
  rewrite H0 in H.
  rewrite H1 in H.
  pose (tod H) ; destruct_exists.
  pose (generation_prod_depth H2) ; destruct_exists.
  exists a a0 b ; intuition ; try apply tposrp_tposr ; auto.
  apply (fromd H3).
  destruct H8.
  destruct H8 ; subst ; auto with coc.
  rewrite H8 ; rewrite H9 in H5.
  apply (fromd H5).
  destruct H8.
  apply tposr_conv with b0 x0 ; auto with coc.
  apply (fromd H5).
  
  pose (thinning_coerce H8 (wf_tposr (fromd H5))). 
  unfold llift in t ; simpl in t.
  auto with coc.

  pose (IHtposrp1 _ _ H1 _ H2) ; destruct_exists.
  pose (IHtposrp2 _ _ H3 _ H2) ; destruct_exists.
  exists a0 b0 c0 ; intuition ; auto with coc.
  apply tposrp_trans with a ; auto with coc.
  pose (tposrp_left_refl H7).
  pose (tposrp_right_refl H4).
  rewrite (tposr_unique_sort t t0).
  assumption.
  apply tposrp_trans with b ; auto with coc.
  apply tposrp_conv_env with (a :: e) ; auto with coc. 
  apply conv_env_hd with c ; auto with coc.
Qed.  

Lemma tposrp_pi : forall e A B T s, tposrp e (Prod_l A B) T (Srt_l s) -> 
  exists3 A' B' s1, T = Prod_l A' B' /\
  tposrp e A A' (Srt_l s1) /\ tposrp (A :: e) B B' (Srt_l s).
Proof.
  intros ; apply tposrp_pi_aux with (Prod_l A B) (Srt_l s) ; auto with coc.
Qed.

Corollary injectivity_of_pi : forall e A A' B B' s, e |-- Prod_l A B ~= Prod_l A' B' : s ->
  exists s1, e |-- A ~= A' : s1 /\ A :: e |-- B ~= B' : s.
Proof.
  intros.
  pose (tposr_eq_cr H) ; destruct_exists.
  pose (tposrp_pi H0).
  pose (tposrp_pi H1).
  destruct_exists.
  rewrite H2 in H3.
  generalize dependent e.
  inversion_clear H3.
  intros.
  pose (tposrp_right_refl H6).
  pose (tposrp_right_refl H4).
  pose (tposr_unique_sort t t0).
  rewrite <- e0 in H4.
  pose (tposrp_tposr_eq H3).
  pose (tposrp_tposr_eq H6).
  pose (tposrp_tposr_eq H7).
  pose (tposrp_tposr_eq H5).
  exists c0.
  assert(e |-- A ~= A' : c0).
  apply tposr_eq_trans with a0 ; auto with coc.
  intuition.
  apply tposr_eq_trans with b0 ; auto with coc.
  apply conv_env_eq with (A' :: e) ; auto with coc.
  apply conv_env_hd with c0 ; auto with coc.
Qed.

Lemma tposrp_sum_aux : forall e T T' Ts, tposrp e T T' Ts -> 
  forall A B, T = Sum_l A B -> forall s, Ts  = Srt_l s -> 
  exists4 A' B' s1 s2, T' = Sum_l A' B' /\
  tposrp e A A' (Srt_l s1) /\ tposrp (A :: e) B B' (Srt_l s2) /\ 
  sum_sort s1 s2 s.
Proof.
  induction 1 ; simpl ; intros.
  
  rewrite H0 in H.
  rewrite H1 in H.
  pose (tod H) ; destruct_exists.
  pose (generation_sum_depth H2) ; destruct_exists.
  exists a a0 b b0 ; intuition ; try apply tposrp_tposr ; auto.
  apply (fromd H3).
  apply (fromd H5).
  rewrite (equiv_eq_sort H9).
  assumption.

  pose (IHtposrp1 _ _ H1 _ H2) ; destruct_exists.
  pose (IHtposrp2 _ _ H3 _ H2) ; destruct_exists.
  exists a0 b0 c0 d0.
  assert(conv_in_env (a :: e) (A :: e)).
  apply conv_env_hd with c ; auto with coc.
  intuition ; auto with coc.
  apply tposrp_trans with a ; auto with coc.
  pose (tposrp_left_refl H8).
  pose (tposrp_right_refl H4).
  rewrite (tposr_unique_sort t t0).
  assumption.
  apply tposrp_trans with b ; auto with coc.
  pose (tposrp_left_refl H9).
  pose (tposrp_right_refl H5).
  assert(tposr (A :: e) b b (Srt_l d0)).
  apply conv_env with (a :: e) ; auto with coc.
  rewrite (tposr_unique_sort H12 t0) ; auto.
  apply tposrp_conv_env with (a :: e) ; auto with coc.
Qed.  

Lemma tposrp_sum : forall e A B T s, tposrp e (Sum_l A B) T (Srt_l s) -> 
  exists4 A' B' s1 s2, T = Sum_l A' B' /\
  tposrp e A A' (Srt_l s1) /\ tposrp (A :: e) B B' (Srt_l s2) /\
  sum_sort s1 s2 s.
Proof.
  intros ; apply tposrp_sum_aux with (Sum_l A B) (Srt_l s) ; auto with coc.
Qed.

Corollary injectivity_of_sum : forall e A A' B B' s, e |-- Sum_l A B ~= Sum_l A' B' : s ->
  exists2 s1 s2, e |-- A ~= A' : s1 /\ A :: e |-- B ~= B' : s2 /\ sum_sort s1 s2 s.
Proof.
  intros.
  pose (tposr_eq_cr H) ; destruct_exists.
  pose (tposrp_sum H0).
  pose (tposrp_sum H1).
  destruct_exists.
  rewrite H2 in H3.
  generalize dependent e.
  inversion_clear H3.
  intros.
  pose (tposrp_right_refl H7).
  pose (tposrp_right_refl H4).
  pose (tposr_unique_sort t t0).
  rewrite <- e0 in H4.
  pose (tposrp_tposr_eq H3).
  pose (tposrp_tposr_eq H7).
  pose (tposrp_tposr_eq H8).
  pose (tposrp_tposr_eq H5).
  exists c0 d0.
  assert(e |-- A ~= A' : c0).
  apply tposr_eq_trans with a0 ; auto with coc.
  intuition.
  apply tposr_eq_trans with b0 ; auto with coc.
  apply conv_env_eq with (A' :: e) ; auto with coc.
  apply tposr_eq_sym.
  pose (tposrp_right_refl H8).
  pose (tposrp_right_refl H5).
  assert(tposr (A :: e) b0 b0 (Srt_l d)).
  apply conv_env with (A' :: e) ; auto with coc.
  apply conv_env_hd with c0 ; auto with coc.
  rewrite (tposr_unique_sort t5 H11).
  assumption.
  apply conv_env_hd with c0 ; auto with coc.
Qed.

Lemma tposrp_subset_aux : forall e T T' Ts, tposrp e T T' Ts -> 
  forall A B, T = Subset_l A B -> forall s, Ts  = Srt_l s -> 
  exists2 A' B', T' = Subset_l A' B' /\
  tposrp e A A' (Srt_l set) /\ tposrp (A :: e) B B' (Srt_l prop).
Proof.
  induction 1 ; simpl ; intros.

  subst.
  pose (generation_subset H) ; destruct_exists.
  exists a b ; split ; auto with coc.

  pose (IHtposrp1 A B H1 s H2).
  destruct_exists.
  pose (IHtposrp2 a b H3 s H2).
  destruct_exists.
  exists a0 b0 ; subst ; intuition ; auto with coc.
  apply tposrp_trans with a ; auto with coc.
  apply tposrp_trans with b ; auto with coc.
  apply tposrp_conv_env with (a :: e) ; auto with coc.
  apply conv_env_hd with set ; auto with coc.
Qed.

Lemma tposrp_subset : forall e  U P T' (s : sort), e |-- Subset_l U P -+> T' : s -> 
  exists2 U' P', T' = Subset_l U' P' /\
  e |-- U -+> U' : set /\ (U :: e) |-- P -+> P' : prop.
Proof.
  intros.
  apply (tposrp_subset_aux H) with s ; auto with coc.
Qed.

Corollary injectivity_of_subset : forall e U P U' P' s, e |-- Subset_l U P ~= Subset_l U' P' : s ->
  e |-- U ~= U' : set /\ U :: e |-- P ~= P' : prop.
Proof.
  intros.
  pose (tposr_eq_cr H) ; destruct_exists.
  pose (tposrp_subset H0).
  pose (tposrp_subset H1).
  destruct_exists.
  subst.
  inversion H2 ; subst.
  split.
  apply tposr_eq_trans with a ; auto with coc.
  apply tposr_eq_trans with b ; auto with coc.
  apply conv_env_eq with (U' :: e) ; auto with coc.
  apply conv_env_hd with set ; auto with coc.
  eauto with coc ecoc.
Qed.