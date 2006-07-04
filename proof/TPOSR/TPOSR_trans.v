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
Require Import Lambda.TPOSR.ChurchRosser.
Require Import Lambda.TPOSR.SubjectReduction.

Set Implicit Arguments.

Hint Resolve tposrp_lred : coc.

Lemma tposrp_abs :  forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B M M', (A :: e) |-- M -+> M' : B -> 
  forall B' s2, (A :: e) |-- B -+> B' : Srt_l s2 -> 
  e |-- Abs_l A M -+> Abs_l A' M' : (Prod_l A B).
Proof. 
  intros.
  apply subject_reduction_p ; eauto with coc ecoc.
  exists (Abs_l A M).
  eapply tposr_abs ; eauto with coc ecoc.
Qed.

Lemma tposrp_prod : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  e |-- Prod_l A B -+> Prod_l A' B' : Srt_l s2.
Proof.
  intros.
  apply subject_reduction_p ; eauto with coc ecoc.
Qed.
  
Lemma tposrp_app : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall M M', e |-- M -+> M' : (Prod_l A B) -> 
  forall N N', e |-- N -+> N' : A ->
  e |-- App_l B M N -+> App_l B' M' N' : lsubst N B.
Proof.
  intros.
  pose (tposrp_lred H).
  pose (tposrp_lred H0).
  pose (tposrp_lred H1).
  pose (tposrp_lred H2).
  apply subject_reduction_p ; auto with coc.
  exists (App_l B M N).
  apply tposr_app with A A s1 s2 ; eauto with coc ecoc.
Qed.

Lemma tposrp_beta : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall M M', (A :: e) |-- M -+> M' : B -> 
  forall N N', e |-- N -+> N' : A ->
  e |-- App_l B (Abs_l A M) N -+> lsubst N' M' : lsubst N B.
Proof.
  intros.
  pose (tposrp_lred H).
  pose (tposrp_lred H0).
  pose (tposrp_lred H1).
  pose (tposrp_lred H2).
  apply subject_reduction_p ; auto with coc ecoc.
  apply lred_par_lred.
  apply trans_lred with (App_l B' (Abs_l A' M') N') ; auto with coc.
  exists (App_l B (Abs_l A M) N).
  apply tposr_app with A A s1 s2 ; auto with coc ecoc.
  eauto with coc.
  eauto with coc.
  apply tposr_abs with s1 B s2 ; eauto with coc ecoc.
  eauto with coc.
Qed.

Lemma tposrp_red : forall e M N A, e |-- M -+> N : A -> 
  forall B s, e |-- A -+> B : Srt_l s ->
  e |-- M -+> N : B.
Proof.
  intros.
  apply subject_reduction_p ; eauto with coc ecoc.
  exists M.
  apply tposr_conv_l with A s ; eauto with coc ecoc.
Qed.  

Lemma tposrp_exp : forall e M N B, e |-- M -+> N : B -> 
  forall A s, e |-- A -+> B : Srt_l s ->
  e |-- M -+> N : A.
Proof.
  intros.
  apply subject_reduction_p ; eauto with coc ecoc.
  exists M.
  apply tposr_conv_l with B s ; eauto with coc ecoc.
Qed. 

Lemma tposrp_subset : forall e A A', e |-- A -+> A' : Srt_l set ->
  forall B B', (A :: e) |-- B -+> B' : Srt_l prop ->
  e |-- Subset_l A B -+> Subset_l A' B' : Srt_l set.
Proof.
  intros.
  apply subject_reduction_p ; eauto with coc ecoc.
Qed.  

Lemma tposrp_sigma : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  e |-- Sum_l A B -+> Sum_l A' B' : Srt_l s3.
Proof.
  intros.
  apply subject_reduction_p ; eauto with coc ecoc.
Qed.
 
Lemma tposrp_pair : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u', e |-- u -+> u' : A ->
  forall v v', e |-- v -+> v' : lsubst u B ->
  e |-- Pair_l (Sum_l A B) u v -+> Pair_l (Sum_l A' B') u' v' : Sum_l A B.
Proof.
  intros.
  pose (tposrp_lred H).
  pose (tposrp_lred H0).
  pose (tposrp_lred H2).
  pose (tposrp_lred H3).
  apply subject_reduction_p ; eauto with coc ecoc.
  exists (Pair_l (Sum_l A B) u v).
  eapply tposr_pair ; eauto with coc ecoc.
Qed.

Lemma tposrp_pi1 : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |-- t -+> t' : Sum_l A B ->
  e |-- Pi1_l (Sum_l A B) t -+> Pi1_l (Sum_l A' B') t' : A.
Proof.
  intros.  
  pose (tposrp_lred H).
  pose (tposrp_lred H0).
  pose (tposrp_lred H2).
  apply subject_reduction_p ; eauto with coc ecoc.
  exists (Pi1_l (Sum_l A B) t).
  eapply tposr_pi1 ; eauto with coc ecoc.
Qed.

Lemma tposrp_pi1_red : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', e |-- Pair_l (Sum_l A B) u v -+> Pair_l (Sum_l A' B') u' v' : Sum_l A B ->
  forall A'', e |-- A'' ~= A : s1 ->
  forall B'', A'' :: e |-- B'' ~= B : s2 ->
  e |-- Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v) -+> u' : A''.
Proof.
  intros.  
  pose (tposrp_lred H).
  pose (tposrp_lred H0).
  pose (tposrp_lred H2).
  apply subject_reduction_p ; eauto with coc ecoc.
  apply lred_par_lred.
  apply trans_lred with (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A' B') u' v')) ; auto with coc.
  exists (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)).
  apply tposr_pi1 with s1 s2 s3 ; eauto with coc ecoc.
  apply tposr_conv_l with (Sum_l A B) s3 ; eauto with coc ecoc.
  apply sigma_functionality with s1 s2 ; eauto with coc ecoc.
  apply conv_env_eq with (A'' :: e) ; eauto with coc ecoc.
Qed.

Lemma tposrp_pi2 : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |-- t -+> t' : Sum_l A B ->
  e |-- Pi2_l (Sum_l A B) t -+> Pi2_l (Sum_l A' B') t' : lsubst (Pi1_l (Sum_l A B) t) B.
Proof.
  intros.  
  pose (tposrp_lred H).
  pose (tposrp_lred H0).
  pose (tposrp_lred H2).
  apply subject_reduction_p ; eauto with coc ecoc.
  exists (Pi2_l (Sum_l A B) t).
  eapply tposr_pi2 ; eauto with coc ecoc.
Qed.

Lemma tposrp_pi2_red : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', 
  e |-- Pair_l (Sum_l A B) u v -+> Pair_l (Sum_l A' B') u' v' : Sum_l A B ->
  forall A'', e |-- A'' ~= A : s1 ->
  forall B'', A'' :: e |-- B'' ~= B : s2 ->
  e |-- Pi2_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v) -+> v' : lsubst (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) B.
Proof.
  intros.  
  pose (tposrp_lred H).
  pose (tposrp_lred H0).
  pose (tposrp_lred H2).
  apply subject_reduction_p ; auto with coc ecoc.
  apply lred_par_lred.
  apply trans_lred with (Pi2_l (Sum_l A'' B'') (Pair_l (Sum_l A' B') u' v')) ; auto with coc.
  exists (Pi2_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)).
  apply tposr_conv_l with (lsubst (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) B'') s2.
  apply substitution_eq with A''  ; auto with coc.
  apply tposr_pi1 with s1 s2 s3 ; auto with coc ecoc.
  eauto with coc.
  eauto with coc.
  apply tposr_conv_l with (Sum_l A B) s3 ; eauto with coc ecoc.
  apply sigma_functionality with s1 s2 ; eauto with coc ecoc.
  apply conv_env_eq with (A'' :: e) ; eauto with coc ecoc.

  apply tposr_pi2 with s1 s2 s3 ; auto with coc ecoc.
  eauto with coc.
  eauto with coc.
  apply tposr_conv_l with (Sum_l A B) s3 ; eauto with coc ecoc.
  apply sigma_functionality with s1 s2 ; eauto with coc ecoc.
  apply conv_env_eq with (A'' :: e) ; eauto with coc ecoc.
Qed.

Lemma tposrp_substitution : forall e d d' t, e |-- d -+> d' : t ->
  forall u u' U, t :: e |-- u -+>  u' : U -> 
  e |-- (lsubst d u) -+> (lsubst d' u') : (lsubst d U).
Proof.
  induction 1 ; simpl ; intros; subst ; eauto with coc ecoc.
  apply tposrp_substitution with Z ; auto.

  apply tposrp_trans with (lsubst X u) ; eauto with coc ecoc.
  destruct (validity_tposrp H1) ; destruct_exists.
  rewrite H2.
  change (lsubst W (Srt_l x)) with (Srt_l x).
  rewrite H2 in H1.
  subst.
  apply (IHtposrp2 u u' (Srt_l x)) ; auto.
  apply tposrp_conv_l with (lsubst X U) b ; eauto with coc ecoc.
  
  pose (left_refl H2).
  pose (tposrp_tposr t).
  pose (IHtposrp1 _ _ _ t0).
  apply tposr_eq_sym.
  apply tposrp_tposr_eq.
  apply t1.
Qed.

Lemma conv_substitution :   forall G d d' s, G |-- d ~= d' : s ->  
  forall u v s', Srt_l s :: G |-- u ~= v : s' ->
  G |-- (lsubst d u) ~= (lsubst d' v) : s'.
Proof.
  intros.
  pose (tposr_eq_cr H).
  pose (tposr_eq_cr H0).
  destruct_exists.  
  apply tposr_eq_trans with (lsubst x0 x).
  apply tposrp_tposr_eq.
  change (Srt_l s') with (lsubst d (Srt_l s')).
  apply (tposrp_substitution H2 H1).
 
  apply tposr_eq_sym.
  apply tposrp_tposr_eq.
  change (Srt_l s') with (lsubst d' (Srt_l s')).
  apply (tposrp_substitution H4 H3).
Qed.
(*
Lemma coerce_conv_substitution :   forall G d d' s, G |-- d >-> d' : s ->  
  forall u v s', Srt_l s :: G |-- u ~= v : s' ->
  G |-- (lsubst d u) >-> (lsubst d' v) : s'.
Proof.
  intros.
  pose (tposr_eq_cr H0).
  destruct_exists.  

  apply tposr_coerce_trans with (lsubst d x).
  apply substitution_coerce with s.
  auto with coc.
  pose (coerce_refl_l H).
  auto with coc.

  induction H.
  apply tposr_coerce_conv.
  apply conv_substitution with s ; auto with coc.
  
  
  
 
  apply tposr_eq_sym.
  apply tposrp_tposr_eq.
  change (Srt_l s') with (lsubst d' (Srt_l s')).
  apply (tposrp_substitution H4 H3).
Qed.

Lemma coerce_substitution_aux :   forall G d d' s, G |-- d >-> d' : s ->  
  forall e u v s', e |-- u >-> v : s' -> e = Srt_l s :: G ->
  G |-- (lsubst d u) >-> (lsubst d' v) : s'.
Proof.
  induction 2 ; simpl ; intros ; subst ; auto with coc.
  
  pose (conv_substitution 

Lemma coerce_substitution :   forall G d d' s, G |-- d >-> d' : s ->  
  forall u v s', Srt_l s :: G |-- u >-> v : s' ->
  G |-- (lsubst d u) >-> (lsubst d' v) : s'.
Proof.
  intros.
  pose (tposr_eq_cr H).
  pose (tposr_eq_cr H0).
  destruct_exists.  
  apply tposr_eq_trans with (lsubst x0 x).
  apply tposrp_tposr_eq.
  change (Srt_l s') with (lsubst d (Srt_l s')).
  apply (tposrp_substitution H2 H1).
 
  apply tposr_eq_sym.
  apply tposrp_tposr_eq.
  change (Srt_l s') with (lsubst d' (Srt_l s')).
  apply (tposrp_substitution H4 H3).
Qed.

  
*)