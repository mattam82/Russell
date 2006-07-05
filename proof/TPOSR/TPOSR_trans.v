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
Require Import Lambda.TPOSR.Coercion.
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

  eapply tposrp_app_aux3 with A s2 A s1 ; auto with coc ecoc.
  apply tposr_conv with (Prod_l A B) s2 ; eauto with coc ecoc.
  apply tposr_coerce_prod with s1 ; eauto with coc ecoc.
  eauto with coc ecoc.  
  eauto with coc ecoc. 
Qed.

Lemma tposrp_beta : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall M M', (A :: e) |-- M -+> M' : B -> 
  forall N N', e |-- N -+> N' : A ->
  e |-- App_l B (Abs_l A M) N -+> lsubst N' M' : lsubst N B.
Proof.
Admitted.
(*  intros.
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
*)
Lemma tposrp_red : forall e M N A, e |-- M -+> N : A -> 
  forall B s, e |-- A -+> B : Srt_l s ->
  e |-- M -+> N : B.
Proof.
Admitted.
(*  intros.
  apply subject_reduction_p ; eauto with coc ecoc.
  exists M.
  apply tposr_conv_l with A s ; eauto with coc ecoc.
Qed.  
*)
Lemma tposrp_exp : forall e M N B, e |-- M -+> N : B -> 
  forall A s, e |-- A -+> B : Srt_l s ->
  e |-- M -+> N : A.
Proof.
Admitted.
(*  intros.
  apply subject_reduction_p ; eauto with coc ecoc.
  exists M.
  apply tposr_conv_l with B s ; eauto with coc ecoc.
Qed. 
*)

Lemma tposrp_subset : forall e A A', e |-- A -+> A' : Srt_l set ->
  forall B B', (A :: e) |-- B -+> B' : Srt_l prop ->
  e |-- Subset_l A B -+> Subset_l A' B' : Srt_l set.
Proof.
Admitted.
(*  intros.
  apply subject_reduction_p ; eauto with coc ecoc.
Qed.  
*)
Lemma tposrp_sigma : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  e |-- Sum_l A B -+> Sum_l A' B' : Srt_l s3.
Proof.
Admitted.
(*  intros.
  apply subject_reduction_p ; eauto with coc ecoc.
Qed.
 *)

Lemma tposrp_pair : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u', e |-- u -+> u' : A ->
  forall v v', e |-- v -+> v' : lsubst u B ->
  e |-- Pair_l (Sum_l A B) u v -+> Pair_l (Sum_l A' B') u' v' : Sum_l A B.
Proof.
Admitted.
(*  intros.
  pose (tposrp_lred H).
  pose (tposrp_lred H0).
  pose (tposrp_lred H2).
  pose (tposrp_lred H3).
  apply subject_reduction_p ; eauto with coc ecoc.
  exists (Pair_l (Sum_l A B) u v).
  eapply tposr_pair ; eauto with coc ecoc.
Qed.*)

Lemma tposrp_pi1 : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |-- t -+> t' : Sum_l A B ->
  e |-- Pi1_l (Sum_l A B) t -+> Pi1_l (Sum_l A' B') t' : A.
Proof.
Admitted.
(*  intros.  
  pose (tposrp_lred H).
  pose (tposrp_lred H0).
  pose (tposrp_lred H2).
  apply subject_reduction_p ; eauto with coc ecoc.
  exists (Pi1_l (Sum_l A B) t).
  eapply tposr_pi1 ; eauto with coc ecoc.
Qed.
*)
Lemma tposrp_pi1_red : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', e |-- Pair_l (Sum_l A B) u v -+> Pair_l (Sum_l A' B') u' v' : Sum_l A B ->
  forall A'', e |-- A'' ~= A : s1 ->
  forall B'', A'' :: e |-- B'' ~= B : s2 ->
  e |-- Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v) -+> u' : A''.
Proof.
Admitted.
(*  intros.  
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
*)
Lemma tposrp_pi2 : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |-- t -+> t' : Sum_l A B ->
  e |-- Pi2_l (Sum_l A B) t -+> Pi2_l (Sum_l A' B') t' : lsubst (Pi1_l (Sum_l A B) t) B.
Proof.
Admitted.
(*  intros.  
  pose (tposrp_lred H).
  pose (tposrp_lred H0).
  pose (tposrp_lred H2).
  apply subject_reduction_p ; eauto with coc ecoc.
  exists (Pi2_l (Sum_l A B) t).
  eapply tposr_pi2 ; eauto with coc ecoc.
Qed.
*)
Lemma tposrp_pi2_red : forall e A A' s1, e |-- A -+> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -+> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', 
  e |-- Pair_l (Sum_l A B) u v -+> Pair_l (Sum_l A' B') u' v' : Sum_l A B ->
  forall A'', e |-- A'' ~= A : s1 ->
  forall B'', A'' :: e |-- B'' ~= B : s2 ->
  e |-- Pi2_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v) -+> v' : lsubst (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) B.
Proof.
Admitted.
(*  intros.  
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
Qed.*)

Lemma tposrp_substitution : forall e d d' t, e |-- d -+> d' : t ->
  forall u u' U, t :: e |-- u -+>  u' : U -> 
  e |-- (lsubst d u) -+> (lsubst d' u') : (lsubst d U).
Proof.
Admitted.
(*  induction 1 ; simpl ; intros; subst ; eauto with coc ecoc.
  apply tposrp_substitution with Z ; auto.

  apply tposrp_trans with (lsubst X u) ; eauto with coc ecoc.
  destruct (validity_tposrp H1) ; destruct_exists.
  rewrite H2.
  change (lsubst W (Srt_l x)) with (Srt_l x).
  rewrite H2 in H1.
  subst.
  apply (IHtposrp2 u u' (Srt_l x)) ; auto.
  apply tposrp_conv_l with (lsubst X U) b ; eauto with coc ecoc.
  
  pose (refl_l H2).
  pose (tposrp_tposr t).
  pose (IHtposrp1 _ _ _ t0).
  apply tposr_eq_sym.
  apply tposrp_tposr_eq.
  apply t1.
Qed.
*)
Lemma conv_substitution :   forall G d d' s, G |-- d ~= d' : s ->  
  forall u v s', Srt_l s :: G |-- u ~= v : s' ->
  G |-- (lsubst d u) ~= (lsubst d' v) : s'.
Proof.
Admitted.
(*  intros.
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
Qed.*)
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