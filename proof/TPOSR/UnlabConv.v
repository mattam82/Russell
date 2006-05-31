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
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.TypesDepth.
Require Import Lambda.TPOSR.TypesFunctionality.
Require Import Lambda.TPOSR.UniquenessOfTypes.
Require Import Lambda.TPOSR.ChurchRosserDepth.
Require Import Lambda.TPOSR.ChurchRosser.
Require Import Lambda.TPOSR.SubjectReduction.
Require Import Lambda.TPOSR.Unlab.
Require Import Lambda.TPOSR.TPOSR_trans.
Set Implicit Arguments.

Hint Unfold tposr_term tposr_term_depth : coc.
Hint Unfold equiv_sort : coc.
Hint Resolve conv_env : coc.

Lemma tposr_term_conv_env : forall e t T, tposr_term e t T ->
  forall f, conv_in_env e f -> tposr_term f t T.
Proof.
  unfold tposr_term ; intros ; destruct_exists.
  exists x ; eauto with coc.
Qed.

Hint Resolve tposr_term_conv_env : coc.

Lemma tposr_unlab_conv : forall M G N A B, tposr_term G M A -> tposr_term G N B ->
  (|M|) = (|N|) ->
  exists P, 
  (G |-- M -+> P : A /\
  G |-- M -+> P : B /\
  G |-- N -+> P : A /\
  G |-- N -+> P : B).
Proof.
  induction M ; unfold tposr_term ; intros ; destruct_exists.

  destruct N ; try (simpl in H1 ; try discriminate) ; intros.
  pose (tposr_sort H).
  pose (tposr_sort H0).
  assert(Srt_l s = Srt_l s0).
  inversion H1 ; auto.
  rewrite H2 in H.
  rewrite H2.
  rewrite e0 in H0.
  rewrite e in H.
  rewrite H2 in H5.
  exists (Srt_l s0) ; intuition ; auto with coc.
  
  (* Var *)
  destruct N ; try (simpl in H1 ; try discriminate) ; intros.
  exists (Ref_l n).
  inversion H1.
  intuition.
  rewrite <- H3.
  apply tposrp_tposr ; apply left_refl with x0; auto.
  apply tposrp_tposr ; apply left_refl with x ; auto.  
  rewrite <- H3.
  apply tposrp_tposr ; apply left_refl with x0; auto.
  apply tposrp_tposr ; apply left_refl with x; auto.

  (* Abs *)
  destruct N ; try (simpl in H1 ; try discriminate) ; intros.
  pose (generation_lambda H).
  pose (generation_lambda H0).
  destruct_exists.
  subst.
  inversion H1.
  subst.
  assert(tposr_term G M1 (Srt_l b2)) by eauto with coc.
  assert(tposr_term G N1 (Srt_l b)) by eauto with coc.

  pose (IHM1 _ _ _ _ H6 H13 H10) ; destruct_exists.
  assert(conv_in_env (M1 :: G) (x :: G)) by eauto with coc.
  assert(conv_in_env (N1 :: G) (x :: G)) by eauto with coc.
  assert(tposr_term (x :: G) M2 a4) by eauto with coc.
  assert(tposr_term (x :: G) N2 a1) by eauto with coc.

  pose (IHM2 _ _ _ _ H20 H21 H12) ; destruct_exists.
  assert(equiv_sort G (Prod_l N1 a1) (Prod_l M1 a4) b0).
  unfold equiv_sort.
  apply pi_functionality with b2 ; eauto with coc.
  apply tposr_eq_trans with x ; eauto with coc.
  apply conv_env_eq with (x :: G) ; auto with coc.
  destruct (tposrp_uniqueness_of_types H22 H23) ; destruct H26.
  subst ; eauto with coc.
  apply tposr_eq_sym.
  assert(x1 = b0) by eauto with coc.
  rewrite <- H27 ; eauto with coc.
  assert(b0 = b3).
  pose (conv_refl_r H11).
  pose (conv_refl_r H26).
  eauto with coc.
  subst.

  assert(equiv_sort G B (Prod_l M1 a4) b3).
  unfold equiv_sort ; apply tposr_eq_trans with (Prod_l N1 a1) ; auto with coc.

  assert(equiv_sort G A (Prod_l N1 a1) b3).
  unfold equiv_sort ; apply tposr_eq_trans with (Prod_l M1 a4) ; auto with coc.
  
  exists (Abs_l x x0) ; intuition.

  apply tposrp_conv_l with (Prod_l M1 a4) b3 ; eauto with coc.
  apply tposrp_abs with b b4 b3 ; eauto with coc.
  apply tposrp_conv_env with (x :: G) ; eauto with coc.

 
  apply tposrp_conv_l with (Prod_l M1 a4) b3 ; eauto with coc.
  apply tposrp_abs with b b4 b3 ; eauto with coc.
  apply tposrp_conv_env with (x :: G) ; eauto with coc.

  apply tposrp_conv_l with (Prod_l N1 a1) b3 ; eauto with coc.
  apply tposrp_abs with b b1 b3 ; eauto with coc.
  apply tposrp_conv_env with (x :: G) ; eauto with coc.

  apply tposrp_conv_l with (Prod_l N1 a1) b3 ; eauto with coc.
  apply tposrp_abs with b b1 b3 ; eauto with coc.
  apply tposrp_conv_env with (x :: G) ; eauto with coc.

  (* App *)
  destruct N ; try (simpl in H1 ; try discriminate).
  pose (generation_app2 H).
  pose (generation_app2 H0).
  destruct_exists.
  inversion H1 ; subst.
  
  assert(tposr_term G M2 (Prod_l a2 M1)) by eauto with coc.
  assert(tposr_term G N2 (Prod_l a N1)) by eauto with coc.
  pose (IHM2 _ _ _ _ H14 H17 H15) ; destruct_exists.
  assert(tposr_term G M3 a2) by eauto with coc.
  assert(tposr_term G N3 a) by eauto with coc.
  pose (IHM3 _ _ _ _ H22 H23 H16) ; destruct_exists.
  
  subst.

  pose (tposrp_uniqueness_of_types H18 H19).
  destruct e ; destruct_exists.
  unfold eq_kind in H28 ; intuition ; try discriminate.
  pose (injectivity_of_pi H28) ; destruct_exists.
  pose (tposr_eq_cr H30) ; destruct_exists.

  assert(G |-- lsubst N3 N1 ~= lsubst M3 M1 : x3).
  apply tposr_eq_trans with (lsubst x2 x5).
  
  apply tposrp_tposr_eq.
  change (Srt_l x3) with (lsubst N3 (Srt_l x3)).
  apply tposrp_substitution with a2 ; auto with coc.
  
  apply tposr_eq_sym.
  apply tposrp_tposr_eq.
  change (Srt_l x3) with (lsubst M3 (Srt_l x3)).
  apply tposrp_substitution with a2 ; auto with coc.

  assert (b3 = x3) by apply (unique_sort (conv_refl_r H12) (conv_refl_r H33)).
  assert(b0 = x3) by apply (unique_sort (conv_refl_r H7) (conv_refl_l H33)).
  subst.

  exists (App_l x5 x1 x2).
  clear H8 H13 ; intuition.

  apply tposrp_conv_l with (lsubst M3 M1) x3 ; auto with coc.
  apply tposrp_app with a2 b2 c0 x3   ; auto with coc.

  apply tposrp_conv_l with (lsubst M3 M1) x3 ; auto with coc.
  apply tposr_eq_trans with (lsubst N3 N1) ; auto with coc.
  apply tposrp_app with a2 b2 c0 x3   ; auto with coc.

  apply tposrp_conv_l with (lsubst N3 N1) x3 ; auto with coc.
  apply tposr_eq_trans with (lsubst M3 M1) ; auto with coc.
  apply tposrp_app with a b c x3 ; auto with coc.
  apply tposrp_conv_env with (a2 :: G) ; eauto with coc.

  apply tposrp_conv_l with (lsubst N3 N1) x3 ; auto with coc.
  apply tposrp_app with a b c x3   ; auto with coc.
  apply tposrp_conv_env with (a2 :: G) ; eauto with coc.

  (* Pair *)
  destruct N ; try (simpl in H1 ; try discriminate).

Admitted.