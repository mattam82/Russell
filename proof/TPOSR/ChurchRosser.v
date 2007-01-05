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
Require Import Lambda.TPOSR.SubstitutionTPOSR.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.CtxCoercion.
Require Import Lambda.TPOSR.CtxConversion.
Require Import Lambda.TPOSR.Equiv.
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.Validity.
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.TypesDepth.
Require Import Lambda.TPOSR.TypesFunctionality.
Require Import Lambda.TPOSR.UniquenessOfTypes.
Require Import Lambda.TPOSR.ChurchRosserDepth.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.

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

Lemma tposrp_n_tposrp :  forall e t u T n, tposrp_n e t u T n -> tposrp e t u T.
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

Lemma tposrp_n_transitive : forall e t u T n, tposrp_n e t u T n -> 
  forall v m, tposrp_n e u v T m ->
  tposrp_n e t v T (n + m).
Proof.
  induction 1 ; intros.
  simpl.
  apply tposrp_n_trans with Y ; auto.
  pose (IHtposrp_n v m0 H1).
  change (S m + m0) with (S (m + m0)).
  apply tposrp_n_trans with X ; auto with coc.
Qed.

Lemma tposrp_tposrp_n : forall e t u T, tposrp e t u T -> 
  exists n, tposrp_n e t u T n.
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
  pose (church_rosser H (refl_l H)) ; destruct_exists.
  exists x ; intuition ; auto with coc.

  destruct_exists.
  exists x ; intuition.

  destruct_exists.
  pose (tposrp_cr H4 H1) ; destruct_exists.
  exists x1 ; intuition.
  apply tposrp_trans with x0 ; auto with coc.
  apply tposrp_trans with x ; auto with coc.
Qed.

Lemma tposr_sort_aux : forall e T T' Ts', tposr e T T' Ts' -> forall s, T = Srt_l s -> T' = Srt_l s.
Proof.
  induction 1 ; intros ; try discriminate ; auto with coc.
Qed. 

Lemma tposr_sort : forall e s T' Ts', tposr e (Srt_l s) T' Ts' -> T' = Srt_l s.
Proof.
  intros ; apply tposr_sort_aux with e (Srt_l s) Ts' ; auto.
Qed. 
 
Lemma tposrp_sort_aux : forall e T T' Ts', tposrp e T T' Ts' -> forall s, T = Srt_l s -> T' = Srt_l s.
Proof.
  induction 1 ; intros.
  rewrite H0 in H.
  pose (generation_sort H).
  intuition.

  pose (IHtposrp1 _ H1).
  apply (IHtposrp2 _ e0).
Qed.

Lemma tposrp_sort : forall e s T' Ts', tposrp e (Srt_l s) T' Ts' -> T' = Srt_l s.
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

Lemma tposr_sort_kinded_depth : forall n e T U V, e |-- T -> U : V [n] ->
  forall s, T = Srt_l s -> V = kind.
Proof.
  intros n.
  pattern n.
  apply wf_lt_induction_type.
  intros x IH m.
  
  destruct 1 ; simpl ; intros ; try discriminate ; auto with coc.

  subst.
  assert(n0 < S n0) by auto with arith.
  pose (IH _ H1 _ _ _ _ H s0 (refl_equal (Srt_l s0))).
  rewrite e0 in H0.
  elim (tposr_not_kind (coerce_refl_l H0)).
Qed.

Lemma tposr_sort_kinded : forall e s V, e |-- s -> s : V -> V = kind.
Proof.
  intros.
  destruct (tod H).
  apply (tposr_sort_kinded_depth H0) with s ; auto.
Qed.  

Lemma in_set_not_sort : forall e t T, e |-- t -> t : T ->
  T = Srt_l set -> forall s, t <> Srt_l s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  red ; intros.
  destruct (inv_subst_sort _ _ _ H3).
  rewrite H5 in H2.
  pose (tposr_sort_kinded (refl_l H2)).
  rewrite e0 in H.
  elim (tposr_not_kind H).
  pose (IHtposr3 H5).
  destruct (inv_subst_sort _ _ _ H4).
  rewrite H6 in H2.
  pose (tposr_sort_kinded (refl_r H2)).
  rewrite e0 in H.
  elim (tposr_not_kind H).
  pose (n s) ; contradiction.
  red ; intros.
  rewrite H2 in H.
  pose (tposr_sort_kinded (refl_r H)).
  rewrite e0 in H0.
  elim (tposr_not_kind (coerce_refl_l H0)).

  rewrite H7 in H3.
  pose (tposr_sort_kinded (refl_l H3)).
  injection e0 ; intros.
  rewrite H8 in H1.
  destruct H1 ; intuition ; try discriminate.
  destruct (inv_subst_sort _ _ _ H7) ; try discriminate.
  rewrite H8 in H5.
  pose (tposr_sort_kinded (coerce_refl_l H5)).
  injection e0 ; intros.
  rewrite H9 in H1.
  destruct H1 ; intuition ; try discriminate.
Qed.

Lemma tposr_sort_eq_aux : forall e t u T, e |-- t -> u : T ->
  forall s, t = Srt_l s -> u = Srt_l s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
Qed.

Lemma tposr_sort_eq : forall e s u T, e |-- s -> u : T -> u = s.
Proof.
  intros ; eapply tposr_sort_eq_aux with e s T ; auto.
Qed.

Lemma tposrp_sort_eq_aux : forall e t u T, e |-- t -+> u : T ->
  forall s, t = Srt_l s -> u = Srt_l s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  apply tposr_sort_eq with e Z ; auto with coc.
  subst ; auto.
Qed.

Lemma tposrp_sort_eq : forall e s u T, e |-- s -+> u : T -> u = s.
Proof.
  intros ; eapply tposrp_sort_eq_aux with e s T ; auto.
Qed.

Lemma tposr_eq_sort_tposrp_aux : forall e t u s, e |-- t ~= u : s ->
  forall s', t = Srt_l s' -> e |-- u -+> Srt_l s' : s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  subst.
  rewrite (tposr_sort_eq H).
  rewrite (tposr_sort_eq H) in H ; auto with coc.

  subst.
  pose (tposr_eq_cr H) ; destruct_exists.
  assert (Heq:=tposrp_sort_eq H1).
  subst.
  assumption.

  subst.
  pose (tposr_eq_trans H H0).
  pose (tposr_eq_cr t) ; destruct_exists.
  pose (tposrp_sort_eq H1).
  rewrite e0 in H2.
  assumption.
Qed.

Lemma tposr_eq_sort_tposrp : forall e s u s', e |-- s ~= u : s' -> 
  e |-- u -+> s : s'.
Proof.
  intros ; eapply tposr_eq_sort_tposrp_aux with s ; auto.
Qed.

Lemma tposr_prod_prod : forall e t u T, e |-- t -> u : T ->
  forall A B, t = Prod_l A B -> exists2 A' B', u = Prod_l A' B'.
Proof. 
  induction 1 ; simpl ; intros ; try discriminate.
  exists A' B' ; auto.
  apply IHtposr with A0 B0 ; auto.
Qed. 

Lemma tposr_sum_sum : forall e t u T, e |-- t -> u : T ->
  forall A B, t = Sum_l A B -> exists2 A' B', u = Sum_l A' B'.
Proof. 
  induction 1 ; simpl ; intros ; try discriminate.
  apply IHtposr with A0 B0 ; auto.
  exists A' B' ; auto.
Qed. 

Lemma tposr_subset_subset : forall e t u T, e |-- t -> u : T ->
  forall A B, t = Subset_l A B -> exists2 A' B', u = Subset_l A' B'.
Proof. 
  induction 1 ; simpl ; intros ; try discriminate.
  apply IHtposr with A0 B0 ; auto.
  exists A' B' ; auto.
Qed. 

Lemma tposrp_prod_prod_aux : forall e t u T, e |-- t -+> u : T ->
  forall A B, t = Prod_l A B -> exists2 A' B', u = Prod_l A' B'.
Proof. 
  induction 1 ; simpl ; intros ; try discriminate.
  eapply tposr_prod_prod with e X Z A B ; auto.
  subst.
  destruct (IHtposrp1 A B) ; auto.
  eapply IHtposrp2 ; eauto with coc.
Qed. 

Lemma tposrp_sum_sum_aux : forall e t u T, e |-- t -+> u : T ->
  forall A B, t = Sum_l A B -> exists2 A' B', u = Sum_l A' B'.
Proof. 
  induction 1 ; simpl ; intros ; try discriminate.
  eapply tposr_sum_sum with e X Z A B ; auto.
  subst.
  destruct (IHtposrp1 A B) ; auto.
  eapply IHtposrp2 ; eauto with coc.
Qed. 

Lemma tposrp_subset_subset_aux : forall e t u T, e |-- t -+> u : T ->
  forall A B, t = Subset_l A B -> exists2 A' B', u = Subset_l A' B'.
Proof. 
  induction 1 ; simpl ; intros ; try discriminate.
  eapply tposr_subset_subset with e X Z A B ; auto.
  subst.
  destruct (IHtposrp1 A B) ; auto.
  eapply IHtposrp2 ; eauto with coc.
Qed. 

Lemma tposrp_prod_prod : forall e A B u T, e |-- Prod_l A B -+> u : T ->
  exists2 A' B', u = Prod_l A' B'.
Proof. 
  intros ; eapply tposrp_prod_prod_aux ; auto with coc.
  apply H.
Qed. 

Lemma tposrp_sum_sum : forall e A B u T, e |-- Sum_l A B -+> u : T ->
  exists2 A' B', u = Sum_l A' B'.
Proof. 
  intros ; eapply tposrp_sum_sum_aux ; auto with coc.
  apply H.
Qed. 

Lemma tposrp_subset_subset : forall e A B u T, e |-- Subset_l A B -+> u : T ->
  exists2 A' B', u = Subset_l A' B'.
Proof. 
  intros ; eapply tposrp_subset_subset_aux ; auto with coc.
  apply H.
Qed. 

Lemma tposr_eq_sort_prod : forall e s t u s', ~ e |-- s ~= Prod_l t u : s'.
Proof.
  red ; intros.
  pose (tposr_eq_sort_tposrp H).
  destruct (tposrp_prod_prod t0) ; discriminate.
Qed.

Lemma tposr_eq_sort_sum : forall e s t u s', ~ e |-- s ~= Sum_l t u : s'.
Proof.
  red ; intros.
  pose (tposr_eq_sort_tposrp H).
  destruct (tposrp_sum_sum t0) ; discriminate.
Qed.

Lemma tposr_eq_sort_subset : forall e s t u s', ~ e |-- s ~= Subset_l t u : s'.
Proof.
  red ; intros.
  pose (tposr_eq_sort_tposrp H).
  destruct (tposrp_subset_subset t0) ; discriminate.
Qed.

Lemma tposr_eq_prod_sum : forall e t u t' u' s', ~ e |-- Prod_l t u ~= Sum_l t' u' : s'.
Proof.
  red ; intros.
  pose (tposr_eq_cr H) ; destruct_exists.
  destruct (tposrp_sum_sum H1).
  destruct (tposrp_prod_prod H0).
  subst ; discriminate.
Qed.

Lemma tposr_eq_prod_subset : forall e t u t' u' s', ~ e |-- Prod_l t u ~= Subset_l t' u' : s'.
Proof.
  red ; intros.
  pose (tposr_eq_cr H) ; destruct_exists.
  destruct (tposrp_prod_prod H0).
  destruct (tposrp_subset_subset H1).
  subst ; discriminate.
Qed.

Lemma tposr_eq_sum_subset : forall e t u t' u' s', ~ e |-- Sum_l t u ~= Subset_l t' u' : s'.
Proof.
  red ; intros.
  pose (tposr_eq_cr H) ; destruct_exists.
  destruct (tposrp_sum_sum H0).
  destruct (tposrp_subset_subset H1).
  subst ; discriminate.
Qed.



Lemma tposr_coerce_sorts : forall e T U s', tposr_coerce e T U s' ->
  forall s, (e |-- T ~= (Srt_l s) : s' -> e |-- U ~= (Srt_l s) : s') /\
  (e |-- U ~= (Srt_l s) : s' -> e |-- T ~= (Srt_l s) : s').
Proof.
  induction 1 ; simpl ; split ; intros ; try discriminate.
  apply tposr_eq_trans with A ; auto with coc.
  apply tposr_eq_trans with B ; auto with coc.

  elim tposr_eq_sort_prod with e s0 A B s' ; auto with coc.
  elim tposr_eq_sort_prod with e s0 A' B' s' ; auto with coc.

  elim tposr_eq_sort_sum with e s0 A B s'' ; auto with coc.
  elim tposr_eq_sort_sum with e s0 A' B' s'' ; auto with coc.

  elim tposr_eq_sort_subset with e s U P set ; auto with coc.

  pose (eq_refl_r H3).
  elim (in_set_not_sort t (refl_equal (Srt_l set))) with s.
  auto.
  pose (eq_refl_r H3).
  elim (in_set_not_sort t (refl_equal (Srt_l set))) with s.
  auto.

  elim tposr_eq_sort_subset with e s U' P set ; auto with coc.

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

Lemma tposr_coerce_sort_l : forall e s u s', e |-- s >-> u : s' -> e |-- u -+> s : s'.
Proof.
  intros e s u s' H.
  destruct (tposr_coerce_sorts H s).
  apply tposr_eq_sort_tposrp.
  assert(e |-- s ~= s : s') by eauto with coc ecoc.
  pose (H0 H2) ; auto with coc.
Qed.

Lemma tposr_coerce_sort_r : forall e s u s', e |-- u >-> s : s' -> e |-- u -+> s : s'.
Proof.
  intros e s u s' H.
  apply tposr_coerce_sort_l ; auto with coc.
Qed.

Lemma tposr_coerce_eq_sort_aux : forall e T U s', tposr_coerce e T U s' ->
  forall s s0, T = (Srt_l s) -> U = (Srt_l s0) -> s = s0.
Proof.
  intros.
  assert(a:=tposr_coerce_sorts H).
  destruct (a s).
  rewrite H0 in H2.
  assert(e |-- s ~= s : s').
  rewrite H0 in H.
  pose (coerce_refl_l H).
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
  pose (tposrp_refl_l H7).
  pose (tposrp_refl_r H4).
  rewrite (unique_sort t t0).
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
  pose (tposrp_refl_r H6).
  assert (t0:=tposrp_refl_r H4).
  pose (unique_sort t t0).
  rewrite <- e0 in H4.
  pose (tposrp_tposr_eq H4).
  pose (tposrp_tposr_eq H6).
  pose (tposrp_tposr_eq H7).
  pose (tposrp_tposr_eq H5).
  exists c0.
  assert(e |-- A ~= A' : c0).
  apply tposr_eq_trans with a0 ; auto with coc.
  intuition.
  apply tposr_eq_trans with b0 ; auto with coc.
  apply eq_conv_env with (A' :: e) ; auto with coc.
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
  pose (tposrp_refl_l H8).
  pose (tposrp_refl_r H4).
  rewrite (unique_sort t t0).
  assumption.
  apply tposrp_trans with b ; auto with coc.
  pose (tposrp_refl_l H9).
  pose (tposrp_refl_r H5).
  assert(tposr (A :: e) b b (Srt_l d0)).
  apply conv_env with (a :: e) ; auto with coc.
  rewrite (unique_sort H12 t0) ; auto.
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
  pose (tposrp_refl_r H7).
  assert(t0:=tposrp_refl_r H4).
  pose (unique_sort t t0).
  rewrite <- e0 in H4.
  pose (tposrp_tposr_eq H4).
  pose (tposrp_tposr_eq H7).
  pose (tposrp_tposr_eq H8).
  pose (tposrp_tposr_eq H5).
  exists c0 d0.
  assert(e |-- A ~= A' : c0).
  apply tposr_eq_trans with a0 ; auto with coc.
  intuition.
  apply tposr_eq_trans with b0 ; auto with coc.
  apply eq_conv_env with (A' :: e) ; auto with coc.
  apply tposr_eq_sym.
  pose (tposrp_refl_r H8).
  pose (tposrp_refl_r H5).
  assert(tposr (A :: e) b0 b0 (Srt_l d)).
  apply conv_env with (A' :: e) ; auto with coc.
  apply conv_env_hd with c0 ; auto with coc.
  rewrite (unique_sort t5 H10).
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
  apply eq_conv_env with (U' :: e) ; auto with coc.
  apply conv_env_hd with set ; auto with coc.
  apply tposr_eq_trans with a ; auto with coc ecoc.
Qed.
