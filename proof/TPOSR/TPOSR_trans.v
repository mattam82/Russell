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
Require Import Lambda.TPOSR.CtxConversion.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.CtxCoercion.
Require Import Lambda.TPOSR.Equiv.
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.Validity.
Require Import Lambda.TPOSR.TypesDepth.
Require Import Lambda.TPOSR.TypesFunctionality.
Require Import Lambda.TPOSR.UniquenessOfTypes.
Require Import Lambda.TPOSR.ChurchRosser.
Require Import Lambda.TPOSR.SubjectReduction.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.

Lemma substitution_tposrp_tposr : forall e d d' t, e |-- d -+> d' : t ->
  forall u u' U, t :: e |-- u ->  u' : U -> 
  e |-- (lsubst d u) -+> (lsubst d' u') : (lsubst d U).
Proof.
  induction 1 ; simpl ; intros.
  apply tposrp_tposr.
  apply substitution_tposr_tposr with Z ; auto.
  apply tposrp_trans with (lsubst X u).
  apply IHtposrp1 ; eauto with coc.
  pose (IHtposrp1 _ _ _ (refl_l H1)).
  pose (IHtposrp2 _ _ _ H1).
  pose (tposr_uniqueness_of_types (tposrp_refl_r t) (tposrp_refl_l t0)).
  apply tposrp_equiv_l with (lsubst X U) ; auto with coc.
Qed.

Lemma substitution_tposrp_coerce : forall e d d' t, e |-- d -+> d' : t ->
  forall u u' s, t :: e |-- u >->  u' : s -> 
  e |-- (lsubst d u) >-> (lsubst d' u') : s.
Proof.
  induction 1 ; simpl ; intros.
  apply substitution_tposr_coerce with Z ; auto.

  apply tposr_coerce_trans with (lsubst X u).
  apply IHtposrp1 ; eauto with coc.
  apply IHtposrp2 ; eauto with coc.
Qed.

Require Import Lambda.TPOSR.Substitution.

Lemma tposrp_abs_aux :  forall e A A' Ts1, e |-- A -+> A' : Ts1 ->
  forall s1, Ts1 = Srt_l s1 ->
  forall B M M', (A :: e) |-- M -> M' : B -> 
  forall B' s2, (A :: e) |-- B -> B' : Srt_l s2 -> 
  e |-- Abs_l A M -+> Abs_l A' M' : (Prod_l A B).
Proof.
  induction 1 ; simpl ; intros ; subst.

  apply tposrp_tposr.
  apply tposr_abs with s1 B' s2 ; auto with coc.

  pose (IHtposrp1 s1 (refl_equal (Srt_l s1)) B M M (refl_l H2) B' s2 H3).
  apply tposrp_trans with (Abs_l X M) ; auto with coc.
  assert(conv_in_env (W :: e) (X :: e)).
  eauto with coc.
  pose (conv_env H2 H1).
  pose (conv_env H3 H1).
  apply tposrp_conv with (Prod_l X B) s2 ; auto with coc.
  apply tposr_coerce_prod with s1 ; eauto with coc.

  apply IHtposrp2 with s1 B' s2 ; auto.
Qed.

Lemma tposrp_abs_aux2 :
  forall G B M M', G |-- M -+> M' : B -> 
  forall e A A' s1, e |-- A -> A' : s1 ->
  G = (A :: e) ->
  forall B' s2, (A :: e) |-- B -> B' : Srt_l s2 -> 
  e |-- Abs_l A M -+> Abs_l A' M' : (Prod_l A B).
Proof.
  induction 1 ; simpl ; intros ; subst.

  apply tposrp_tposr.
  apply tposr_abs with s1 B' s2 ; auto with coc.

  apply tposrp_trans with (Abs_l A X) ; auto with coc.
  apply IHtposrp1 with s1 B' s2 ; auto with coc.
  apply (refl_l H1).
  apply IHtposrp2 with s1 B' s2 ; auto.
Qed.

Hint Resolve conv_env tposrp_conv_env : ecoc.

Lemma tposrp_abs :  forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B M M', (A :: e) |-- M -+> M' : B -> 
  forall B' s2, (A :: e) |-- B -+> B' : Srt_l s2 -> 
  e |-- Abs_l A M -+> Abs_l A' M' : (Prod_l A B).
Proof. 
  intros.
  pose (tposrp_refl_l H0).
  pose (tposrp_refl_l H1).
  apply tposrp_trans with (Abs_l A' M).
  eapply tposrp_abs_aux ; eauto with coc.
  assert(conv_in_env (A :: e) (A' :: e)) by (apply conv_env_hd with s1 ; auto with coc).
  apply tposrp_conv with (Prod_l A' B) s2.
  apply tposr_coerce_prod with s1 ; eauto with coc ecoc.
  eapply tposrp_abs_aux2 ; auto with coc.
  apply tposrp_conv_env with (A :: e) ; auto with coc.
  eauto with coc ecoc.
  apply conv_env with (A :: e) ; auto with coc.
  apply (tposrp_refl_l H1).
Qed.

Ltac conv_in_env X Y e s :=
  assert(conv_in_env (X :: e) (Y :: e)) by (apply conv_env_hd with s ; auto with coc).

Ltac coerce_in_env X Y e s :=
  assert(coerce_in_env (X :: e) (Y :: e)) by (apply coerce_env_hd with s ; auto with coc ecoc).

Lemma tposrp_prod_aux : forall e A A' Ts1, e |-- A -+> A' : Ts1 ->
  forall s1, Ts1 = Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  e |-- Prod_l A B -+> Prod_l A' B' : Srt_l s2.
Proof.
  induction 1 ; simpl ; intros ; subst.

  apply tposrp_tposr.
  apply tposr_prod with s1 ; auto with coc.

  apply tposrp_trans with (Prod_l X B) ; auto with coc.
  apply IHtposrp1 with s1 ; auto with coc.
  eauto with coc.

  apply IHtposrp2 with s1 ; auto.
  conv_in_env X W e s1.
  eauto with coc ecoc.
Qed.

Lemma tposrp_prod : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  e |-- Prod_l A B -+> Prod_l A' B' : Srt_l s2.
Proof.
  intros.

  apply tposrp_trans with (Prod_l A' B).
  eapply tposrp_prod_aux ; auto with coc.
  apply H.
  eauto with coc.

  induction_with_subterms (A :: e) (Srt_l s2) H0.
  apply tposrp_tposr.
  conv_in_env A' A e s1.
  apply tposr_prod with s1 ; eauto with coc ecoc.

  apply tposrp_trans with (Prod_l A' X) ; auto with coc.
Qed.

Ltac induction_ws := induction_with_subterm.
Ltac induction_ws2 := induction_with_subterms.

Lemma tposrp_app_aux : 
  forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall M M', e |-- M -> M' : (Prod_l A B) -> 
  forall N N', e |-- N -> N' : A ->
  e |-- App_l B M N -+> App_l B' M' N' : lsubst N B.
Proof.
  intros e A A' s1 H.
  induction_ws (Srt_l s1) H ; intros.

  apply tposrp_tposr.
  apply tposr_app with X Y s1 s2 ; eauto with coc.
  
  apply IHtposrp1 with s2 ; auto with coc.
Qed.

Lemma tposrp_app_aux2 :
  forall e M M' A B, e |-- M -+> M' : (Prod_l A B) -> 
  forall B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall A' s1, e |-- A -> A' : Srt_l s1 ->
  forall N N', e |-- N -> N' : A ->
  e |-- App_l B M N -+> App_l B' M' N' : lsubst N B.
Proof.
  intros e M M' A B H.
  induction_ws (Prod_l A B) H ; intros.

  apply tposrp_tposr.
  apply tposr_app with A A s1 s2 ; eauto with coc.
  
  apply tposrp_trans with (App_l B X N).
  apply IHtposrp1 with s2 A' s1 ; eauto with coc ecoc.

  eapply IHtposrp2 ; eauto with coc.
Qed.

Lemma tposrp_app_aux3 :
  forall e N N' A, e |-- N -+> N' : A ->
  forall M M' B, e |-- M -> M' : (Prod_l A B) -> 
  forall B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall A' s1, e |-- A -> A' : Srt_l s1 ->
  e |-- App_l B M N -+> App_l B' M' N' : lsubst N B.
Proof.
  intros e N N' A H.
  induction H ; intros.

  apply tposrp_tposr.
  apply tposr_app with Z A' s1 s2 ; eauto with coc.
  
  apply tposrp_trans with (App_l B M X).
  apply IHtposrp1 with s2 A' s1 ; eauto with coc ecoc.

  apply tposrp_conv with (lsubst X B) s2 ; auto with coc.
  apply tposr_coerce_sym.
  apply substitution_coerce_tposrp with Z ; eauto with coc ecoc.
  
  eapply IHtposrp2 ; eauto with coc.
Qed.

Lemma tposrp_app : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall M M', e |-- M -+> M' : (Prod_l A B) -> 
  forall N N', e |-- N -+> N' : A ->
  e |-- App_l B M N -+> App_l B' M' N' : lsubst N B.
Proof.
  intros.
  apply tposrp_trans with (App_l B' M N) ; auto with coc.

  eapply tposrp_app_aux ; eauto with coc.

  apply tposrp_conv with (lsubst N B') s2 ; auto with coc.
  apply substitution_coerce with A ; eauto with coc.

  apply tposrp_trans with (App_l B' M' N) ; auto with coc.

  eapply tposrp_app_aux2 ; eauto with coc ecoc.
  apply tposrp_conv with (Prod_l A B) s2 ; auto with coc.
  apply tposr_coerce_prod with s1 ; eauto with coc ecoc.

  assert(coerce_in_env (A :: e) (A' :: e)).
  apply coerce_env_hd with s1 ; eauto with coc ecoc.
  assert(e |-- Prod_l A B >-> Prod_l A B' : s2).
  apply tposr_coerce_prod with s1 ; eauto with coc ecoc.

  eapply tposrp_app_aux3 with A s2 A s1 ; auto with coc ecoc.
  apply tposr_conv with (Prod_l A B) s2 ; eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc. 
Qed.

(*
Lemma tposrp_beta : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall M M', (A :: e) |-- M -+> M' : B -> 
  forall N N', e |-- N -+> N' : A ->
  e |-- App_l B (Abs_l A M) N -+> lsubst N' M' : lsubst N B.
Proof.

Lemma tposrp_red : forall e M N A, e |-- M -+> N : A -> 
  forall B s, e |-- A -+> B : Srt_l s ->
  e |-- M -+> N : B.
Proof.

Lemma tposrp_exp : forall e M N B, e |-- M -+> N : B -> 
  forall A s, e |-- A -+> B : Srt_l s ->
  e |-- M -+> N : A.
Proof.
*)

Lemma tposrp_subset_aux : forall e A A', e |-- A -+> A' : Srt_l set ->
  forall B B', (A :: e) |-- B -> B' : Srt_l prop ->
  e |-- Subset_l A B -+> Subset_l A' B' : Srt_l set.
Proof.
  intros e A A' H.
  induction_ws (Srt_l set) H ; simpl ; intros ; subst.

  apply tposrp_tposr.
  apply tposr_subset ; auto with coc.

  apply tposrp_trans with (Subset_l X B) ; auto with coc.
  apply IHtposrp1  ; auto with coc.
  eauto with coc.

  apply IHtposrp2 ; auto.
  coerce_in_env W X e set.
  apply tposr_coerce_env with (W :: e) ; auto.
Qed.

Lemma tposrp_subset : forall e A A', e |-- A -+> A' : Srt_l set ->
  forall B B', (A :: e) |-- B -+> B' : Srt_l prop ->
  e |-- Subset_l A B -+> Subset_l A' B' : Srt_l set.
Proof.
  intros.

  apply tposrp_trans with (Subset_l A' B).
  eapply tposrp_subset_aux ; eauto with coc ecoc.

  induction_with_subterms (A :: e) (Srt_l prop) H0.
  apply tposrp_tposr.
  conv_in_env A A' e set.
  apply tposr_subset ; eauto with coc ecoc.

  apply tposrp_trans with (Subset_l A' X) ; auto with coc.
Qed.

Lemma tposrp_sigma_aux : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  e |-- Sum_l A B -+> Sum_l A' B' : Srt_l s3.
Proof.
  intros e A A' s1 H.
  induction_ws (Srt_l s1) H ; simpl ; intros ; subst.

  apply tposrp_tposr.
  apply tposr_sum with s1 s2 ; auto with coc.

  apply tposrp_trans with (Sum_l X B) ; auto with coc.
  apply IHtposrp1 with s2  ; auto with coc.
  eauto with coc.

  apply IHtposrp2 with s2 ; auto.
  coerce_in_env W X e s1.
  apply tposr_coerce_env with (W :: e) ; auto.
Qed.

Lemma tposrp_sigma : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  e |-- Sum_l A B -+> Sum_l A' B' : Srt_l s3.
Proof.
  intros.

  apply tposrp_trans with (Sum_l A' B).
  eapply tposrp_sigma_aux ; eauto with coc ecoc.

  induction_with_subterms (A :: e) (Srt_l s2) H0.
  apply tposrp_tposr.
  conv_in_env A A' e s1.
  apply tposr_sum with s1 s2 ; eauto with coc ecoc.

  apply tposrp_trans with (Sum_l A' X) ; auto with coc.
Qed.

Lemma tposrp_pair_aux1 : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u', e |-- u -> u' : A ->
  forall v v', e |-- v -> v' : lsubst u B ->
  e |-- Pair_l (Sum_l A B) u v -+> Pair_l (Sum_l A' B') u' v' : Sum_l A B.
Proof.
  intros e A A' s1 H.
  induction_ws (Srt_l s1) H ; simpl ; intros ; subst.

  apply tposrp_tposr.
  apply tposr_pair with s1 s2 s3 ; auto with coc.

  apply tposrp_trans with (Pair_l (Sum_l X B) u v) ; auto with coc.
  apply IHtposrp1 with s2 s3 ; auto with coc.
  eauto with coc.
  eauto with coc.
  eauto with coc.

  coerce_in_env W X e s1.

  apply tposrp_conv with (Sum_l X B) s3 ; auto.
  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.

  apply IHtposrp2 with s2 s3 ; auto.
  eauto with coc ecoc.
  eauto with coc.
Qed.

Lemma tposrp_pair_aux2 :
  forall e A B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall A' s1, e |-- A -> A' : Srt_l s1 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u', e |-- u -> u' : A ->
  forall v v', e |-- v -> v' : lsubst u B ->
  e |-- Pair_l (Sum_l A B) u v -+> Pair_l (Sum_l A' B') u' v' : Sum_l A B.
Proof.
  intros e A B B' s2 H.
  induction_ws2 (A :: e) (Srt_l s2) H ; simpl ; intros ; subst.
 
  apply tposrp_tposr.
  apply tposr_pair with s1 s2 s3 ; auto with coc.

  apply tposrp_trans with (Pair_l (Sum_l A X) u v) ; auto with coc.
  apply IHtposrp1 with s1 s3 ; eauto with coc.

  apply tposrp_conv with (Sum_l A X) s3 ; auto.
  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.

  apply IHtposrp2 with s1 s3 ; auto.
  apply tposr_conv with (lsubst u W) s2.
  eauto with coc ecoc.
  apply substitution_coerce with A ; auto with coc.
  eauto with coc.
Qed.

Lemma tposrp_pair_aux3 :
  forall e u u' A, e |-- u -+> u' : A ->
  forall A' s1, e |-- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall v v', e |-- v -> v' : lsubst u B ->
  e |-- Pair_l (Sum_l A B) u v -+> Pair_l (Sum_l A' B') u' v' : Sum_l A B.
Proof.
  intros e u u' A H.
  induction H ; simpl ; intros ; subst.
 
  apply tposrp_tposr.
  apply tposr_pair with s1 s2 s3 ; auto with coc.

  apply tposrp_trans with (Pair_l (Sum_l Z B) X v) ; auto with coc.
  apply IHtposrp1 with s1 s2 s3 ; eauto with coc.

  apply IHtposrp2 with s1 s2 s3 ; auto.
  apply tposr_conv with (lsubst W B) s2.
  eauto with coc ecoc.
  apply substitution_tposrp_coerce with Z ; auto with coc.
  eauto with coc.
Qed.


Lemma tposrp_pair_aux4 :
  forall e u v v' B, e |-- v -+> v' : lsubst u B ->
  forall A A' s1, e |-- A -> A' : Srt_l s1 ->
  forall B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u', e |-- u -> u' : A ->
  e |-- Pair_l (Sum_l A B) u v -+> Pair_l (Sum_l A' B') u' v' : Sum_l A B.
Proof.
  intros e u v v' B H.
  induction_ws (lsubst u B) H ; simpl ; intros ; subst.
 
  apply tposrp_tposr.
  apply tposr_pair with s1 s2 s3 ; auto with coc.

  apply tposrp_trans with (Pair_l (Sum_l A B) u X) ; auto with coc.
  apply IHtposrp1 with s1 s2 s3 ; eauto with coc.

  apply IHtposrp2 with s1 s2 s3 ; auto.
Qed.

Lemma tposrp_pair : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u', e |-- u -+> u' : A ->
  forall v v', e |-- v -+> v' : lsubst u B ->
  e |-- Pair_l (Sum_l A B) u v -+> Pair_l (Sum_l A' B') u' v' : Sum_l A B.
Proof.
  intros.
  apply tposrp_trans with (Pair_l (Sum_l A' B) u v) ; auto with coc.
  apply tposrp_pair_aux1 with s1 s2 s3 ; eauto with coc ecoc.

  assert(e |-- A >-> A' : s1) by eauto with coc.
  assert(coerce_in_env (A :: e) (A' :: e)).
  eauto with coc ecoc.
  pose (tposrp_coerce_env H0 H5).
  pose (tposrp_conv H4 H2).
  apply tposrp_conv with (Sum_l A' B) s3 ; auto with coc.
  apply tposr_coerce_sym.
  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.

  apply tposrp_trans with (Pair_l (Sum_l A' B') u v) ; auto with coc.
  apply tposrp_pair_aux2 with s2 s1 s3 ; eauto with coc ecoc.
  
  apply tposrp_conv with (Sum_l A' B') s3.
  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.
  
  apply tposrp_trans with (Pair_l (Sum_l A' B') u' v) ; auto with coc.
  apply tposrp_pair_aux3 with s1 s2 s3 ; auto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc.
  apply tposr_conv with (lsubst u B) s2 ; eauto with coc.
  apply substitution_tposr_coerce with A ; eauto with coc ecoc.
  
  apply tposrp_pair_aux4 with s1 s2 s3 ; auto with coc ecoc.
  apply tposrp_conv with (lsubst u B) s2 ; eauto with coc.
  apply substitution_tposrp_coerce with A ; eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
Qed. 

Lemma tposrp_pi1_aux :
  forall e t t' A B , e |-- t -+> t' : Sum_l A B ->
  forall A' s1, e |-- A >-> A' : s1 ->
  forall B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  e |-- Pi1_l (Sum_l A B) t -+> Pi1_l (Sum_l A' B') t' : A.
Proof.
  intros e t t' A B H.
  induction_ws (Sum_l A B) H ; simpl ; intros ; subst.
  apply tposrp_tposr.
  apply tposr_pi1 with s1 s2 s3 ; auto with coc.
  eauto with coc.

  apply tposrp_trans with (Pi1_l (Sum_l A B) X).
  apply IHtposrp1 with s1 s2 s3 ; eauto with coc ecoc.

  apply IHtposrp2 with s1 s2 s3 ; eauto with coc ecoc.
Qed.

Lemma tposrp_pi1 :
  forall e A A' s1, e |-- A >-> A' : s1 ->
  forall B B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |-- t -+> t' : Sum_l A B ->
  e |-- Pi1_l (Sum_l A B) t -+> Pi1_l (Sum_l A' B') t' : A.
Proof.
  intros ; apply tposrp_pi1_aux with s1 s2 s3 ; auto with coc.
Qed.

Lemma tposrp_pi2_aux : forall e t t' A B, e |-- t -+> t' : Sum_l A B ->
  forall A' s1, e |-- A >-> A' : s1 ->
  forall B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  e |-- Pi2_l (Sum_l A B) t -+> Pi2_l (Sum_l A' B') t' : lsubst (Pi1_l (Sum_l A B) t) B.
Proof.
  intros e t t' A B H.
  induction_ws (Sum_l A B) H ; simpl ; intros ; subst.
  apply tposrp_tposr.
  apply tposr_pi2 with s1 s2 s3 ; auto with coc.
  eauto with coc.

  apply tposrp_trans with (Pi2_l (Sum_l A B) X).
  apply IHtposrp1 with s1 s2 s3 ; eauto with coc ecoc.

  apply tposrp_conv with (lsubst (Pi1_l (Sum_l A B) X) B) s2.
  apply tposr_coerce_sym.
  apply substitution_tposrp_coerce with A ; auto with coc.
  apply tposrp_pi1 with s1 s2 s3 ; eauto with coc ecoc.
  eauto with coc ecoc.

  apply IHtposrp2 with s1 s2 s3 ; eauto with coc ecoc.
Qed.

Lemma tposrp_pi2 : forall e A A' s1, e |-- A >-> A' : s1 ->
  forall B B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |-- t -+> t' : Sum_l A B ->
  e |-- Pi2_l (Sum_l A B) t -+> Pi2_l (Sum_l A' B') t' : lsubst (Pi1_l (Sum_l A B) t) B.
Proof.
  intros ; apply tposrp_pi2_aux with s1 s2 s3 ; auto with coc.
Qed.
