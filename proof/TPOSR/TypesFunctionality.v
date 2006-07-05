Require Import Lambda.Utils.
Require Import Lambda.Tactics.
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
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.TypesDepth.

Set Implicit Arguments.

Lemma pi_conv_right_aux : 
  forall G' X Y Y' s2, G' |-- Y ~= Y' : s2 ->
  forall G, G' = X :: G ->
  forall s1, G |-- X -> X : Srt_l s1 ->
  G |-- Prod_l X Y ~= Prod_l X Y' : s2.
Proof.
  intros G X Y Y' s2 H.
  induction H ; simpl ; intros ; auto with coc.

  apply tposr_eq_tposr.
  apply tposr_prod with s1 ; auto.
  rewrite <- H0 ; assumption.
  
  apply tposr_eq_sym.
  apply IHtposr_eq with s1 ; auto.
  
  apply tposr_eq_trans with (Prod_l X X0) ; auto.
  apply IHtposr_eq1 with s1 ; auto.
  apply IHtposr_eq2 with s1 ; auto.
Qed.

Lemma pi_conv_right :
  forall G X s1, G |-- X -> X : Srt_l s1 ->
  forall Y Y' s2, X :: G |-- Y ~= Y' : s2 ->
  G |-- Prod_l X Y ~= Prod_l X Y' : s2.
Proof.
  intros ; eapply pi_conv_right_aux ; auto ; auto.
  apply H.
Qed.

Lemma pi_conv_left : 
  forall G X X' s1, G |-- X ~= X' : s1 ->
  forall Y s2, X :: G |-- Y -> Y : Srt_l s2 ->
  G |-- Prod_l X Y ~= Prod_l X' Y : s2.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.

  apply tposr_eq_tposr.
  apply tposr_prod with s ; auto.
  
  apply tposr_eq_sym.
  apply IHtposr_eq ; auto.
  apply conv_env with (Y :: e) ; auto.
  apply conv_env_hd with s ; auto with coc.
  
  apply tposr_eq_trans with (Prod_l X Y0) ; auto.
  apply IHtposr_eq2 ; auto.
  apply conv_env with (W :: e) ; auto.
  apply conv_env_hd with s ; auto with coc.
Qed.

Theorem pi_functionality : forall G X X' s1, G |-- X ~= X' : s1 ->
  forall Y Y' s2, X :: G |-- Y ~= Y' : s2 -> 
  G |-- Prod_l X Y ~= Prod_l X' Y' : s2.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.

  apply tposr_eq_trans with (Prod_l Y Y0) ; auto.
  destruct (conv_refls H0).
  apply pi_conv_left with s ; auto with coc.
  apply pi_conv_right with s ; auto with coc.
  apply (refl_r H).
  apply conv_env_eq with (X :: e) ; auto with coc.
  apply conv_env_hd with s ; auto with coc.

  apply tposr_eq_sym.
  apply IHtposr_eq.
  apply conv_env_eq with (Y :: e) ; auto with coc.
  apply conv_env_hd with s ; auto with coc.

  apply tposr_eq_trans with (Prod_l X Y0) ; auto with coc.
  apply IHtposr_eq1.
  destruct(conv_refls H1).
  auto with coc.

  apply IHtposr_eq2.
  apply conv_env_eq with (W :: e) ; auto with coc.
  apply conv_env_hd with s ; auto with coc.
Qed. 

Lemma sum_conv_right_aux : 
  forall G' X Y Y' s2, G' |-- Y ~= Y' : s2 ->
  forall G, G' = X :: G ->
  forall s1, G |-- X -> X : Srt_l s1 ->
  forall s3, sum_sort s1 s2 s3  ->
  G |-- Sum_l X Y ~= Sum_l X Y' : s3.
Proof.
  intros G X Y Y' s2 H.
  induction H ; simpl ; intros ; auto with coc.

  apply tposr_eq_tposr.
  apply tposr_sum with s1 s ; auto.
  rewrite <- H0 ; assumption.
  
  apply tposr_eq_sym.
  apply IHtposr_eq with s1 ; auto.
  
  apply tposr_eq_trans with (Sum_l X X0) ; auto.
  apply IHtposr_eq1 with s1 ; auto.
  apply IHtposr_eq2 with s1 ; auto.
Qed.

Lemma sum_conv_right :
  forall G X s1, G |-- X -> X : Srt_l s1 ->
  forall Y Y' s2, X :: G |-- Y ~= Y' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  G |-- Sum_l X Y ~= Sum_l X Y' : s3.
Proof.
  intros.
  eapply (@sum_conv_right_aux _ X Y Y' s2 H0) ; auto ; auto ; auto.
  apply H.
  apply H1.
Qed.

Lemma sum_conv_left : 
  forall G X X' s1, G |-- X ~= X' : s1 ->
  forall Y s2, X :: G |-- Y -> Y : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  G |-- Sum_l X Y ~= Sum_l X' Y : s3.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.

  apply tposr_eq_tposr.
  apply tposr_sum with s s2 ; auto.
  
  apply tposr_eq_sym.
  apply IHtposr_eq with s2 ; auto.
  apply conv_env with (Y :: e) ; auto.
  apply conv_env_hd with s ; auto with coc.
  
  apply tposr_eq_trans with (Sum_l X Y0) ; auto.
  apply IHtposr_eq1 with s2 ; auto.
  apply IHtposr_eq2 with s2 ; auto.
  apply conv_env with (W :: e) ; auto.
  apply conv_env_hd with s ; auto with coc.
Qed.

Theorem sigma_functionality : forall G X X' s1, G |-- X ~= X' : s1 ->
  forall Y Y' s2, X :: G |-- Y ~= Y' : s2 -> 
  forall s3, sum_sort s1 s2 s3 ->
  G |-- Sum_l X Y ~= Sum_l X' Y' : s3.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.

  apply tposr_eq_trans with (Sum_l Y Y0) ; auto.
  destruct (conv_refls H0).
  apply sum_conv_left with s s2 ; auto with coc.
  apply sum_conv_right with s s2 ; auto with coc.
  apply (refl_r H).
  apply conv_env_eq with (X :: e) ; auto with coc.
  apply conv_env_hd with s ; auto with coc.

  apply tposr_eq_sym.
  apply IHtposr_eq with s2.
  apply conv_env_eq with (Y :: e) ; auto with coc.
  apply conv_env_hd with s ; auto with coc.
  assumption.

  apply tposr_eq_trans with (Sum_l X Y0) ; auto with coc.
  apply IHtposr_eq1 with s2.
  destruct(conv_refls H1).
  auto with coc.

  assumption.

  apply IHtposr_eq2 with s2.
  apply conv_env_eq with (W :: e) ; auto with coc.
  apply conv_env_hd with s ; auto with coc.
  assumption.
Qed. 

Lemma subset_conv_right_aux : 
  forall G' X Y Y' s, G' |-- Y ~= Y' : s ->
  s = prop ->
  forall G, G' = X :: G -> G |-- X -> X : Srt_l set ->
  G |-- Subset_l X Y ~= Subset_l X Y' : set.
Proof.
  intros G X Y Y' s H.
  induction H ; simpl ; intros ; auto with coc.

  apply tposr_eq_tposr.
  apply tposr_subset ; auto.
  rewrite <- H0 ; rewrite <- H1 ; assumption.
  
  apply tposr_eq_trans with (Subset_l X X0) ; auto.
Qed.

Lemma subset_conv_right :
  forall G X, G |-- X -> X : Srt_l set ->
  forall Y Y', X :: G |-- Y ~= Y' : prop ->
  G |-- Subset_l X Y ~= Subset_l X Y' : set.
Proof.
  intros ; eapply subset_conv_right_aux ; auto ; auto.
Qed.

Lemma subset_conv_left : 
  forall G X X' s, G |-- X ~= X' : s ->
  s = set ->
  forall Y, X :: G |-- Y -> Y : Srt_l prop ->
  G |-- Subset_l X Y ~= Subset_l X' Y : set.
Proof.
  induction 1 ; simpl ; intros ; try rewrite H0 in H ; auto with coc.

  apply tposr_eq_sym.
  apply IHtposr_eq ; auto.
  apply conv_env with (Y :: e) ; auto.
  apply conv_env_hd with set ; auto with coc.

  apply tposr_eq_trans with (Subset_l X Y0) ; auto.
  apply IHtposr_eq2 ; auto.
  apply conv_env with (W :: e) ; auto.
  apply conv_env_hd with s ; auto with coc.
Qed.

Lemma subset_functionality_aux : 
  forall G X X' s, G |-- X ~= X' : s ->
  s = set ->
  forall Y Y', X :: G |-- Y ~= Y' : prop -> 
  G |-- Subset_l X Y ~= Subset_l X' Y' : set.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.

  apply tposr_eq_trans with (Subset_l Y Y0) ; auto.
  destruct (conv_refls H1).
  apply subset_conv_left with s ; auto with coc.
  apply subset_conv_right ; auto with coc.
  rewrite <- H0.
  apply (refl_r H).
  apply conv_env_eq with (X :: e) ; auto with coc.
  apply conv_env_hd with s ; auto with coc.

  apply tposr_eq_sym.
  apply IHtposr_eq ; auto.
  apply conv_env_eq with (Y :: e) ; auto with coc.
  apply conv_env_hd with s ; auto with coc.

  apply tposr_eq_trans with (Subset_l X Y0) ; auto with coc.
  apply IHtposr_eq1 ; auto.
  destruct(conv_refls H2) ; auto with coc.

  apply IHtposr_eq2 ; auto.
  apply conv_env_eq with (W :: e) ; auto with coc.
  apply conv_env_hd with s ; auto with coc.
Qed. 

Corollary subset_functionality : 
  forall G X X', G |-- X ~= X' : set ->
  forall Y Y', X :: G |-- Y ~= Y' : prop -> 
  G |-- Subset_l X Y ~= Subset_l X' Y' : set.
Proof.
  intros ; apply subset_functionality_aux with set ; auto.
Qed.
