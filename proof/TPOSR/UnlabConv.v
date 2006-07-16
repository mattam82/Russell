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
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.Validity.
Require Import Lambda.TPOSR.TypesDepth.
Require Import Lambda.TPOSR.TypesFunctionality.
Require Import Lambda.TPOSR.UniquenessOfTypes.
Require Import Lambda.TPOSR.ChurchRosserDepth.
Require Import Lambda.TPOSR.ChurchRosser.
Require Import Lambda.TPOSR.Injectivity.
Require Import Lambda.TPOSR.SubjectReduction.
Require Import Lambda.TPOSR.Unlab.
Require Import Lambda.TPOSR.TPOSR_trans.
Set Implicit Arguments.

Implicit Types s : sort.

Hint Unfold tposr_term tposr_term_depth : coc.
Hint Unfold equiv_sort : coc.
Hint Resolve conv_env : coc.

Lemma equiv_sort_strenghten : forall G s s', equiv G s s' -> forall e, tposr_wf e -> equiv e s s'.
Proof.
  induction 1.
  intros.
  left.
  assumption.

  intros.
  destruct_exists.
  right.
  exists x.

  pose (tposr_coerce_eq_sort H).
  rewrite e0.
  assert (Heq:=tposr_sort_kinded (coerce_refl_r H)).
  injection Heq.
  intros.
  rewrite H1.
  induction s'.
  elim (tposr_not_kind (coerce_refl_r H)).
  apply tposr_coerce_conv ; apply tposr_eq_tposr ; auto with coc ecoc.
  apply tposr_coerce_conv ; apply tposr_eq_tposr ; auto with coc ecoc.
Qed.

Lemma tposr_sort_strenghten : forall G s s', G |-- s -> s : s' -> forall e, tposr_wf e -> e |-- s -> s : s'.
Proof.
  intros G s s' H.
  assert(equiv G s s) by eauto with coc ecoc.
  intros.
  pose (equiv_sort_strenghten H0 H1).
  destruct e0 ; destruct_exists.
  destruct H2.
  injection H2 ; intros ; subst s.
  elim (tposr_not_kind H).
  pose (coerce_refl_l H2).
  pose (tposr_sort_kinded t).
  rewrite e0 in t.
  pose (tposr_sort_kinded H).
  rewrite e1 ; auto.
Qed.

Lemma tposr_term_conv_env : forall e t T, tposr_term e t T ->
  forall f, conv_in_env e f -> tposr_term f t T.
Proof.
  unfold tposr_term ; intros ; destruct_exists.
  exists x ; eauto with coc ecoc.
Qed.

Hint Resolve tposr_term_conv_env : coc.


Lemma generation_pi1_alt :
  forall e T M X C, e |-- Pi1_l T M -> X : C ->
  exists2 A B, T = Sum_l A B /\ equiv e C A /\
  exists4 A' B' s1 s2, 
  e |-- A >-> A' : s1 /\ A :: e |-- B >-> B' : s2 /\
  exists M', e |-- M -> M' : Sum_l A B /\
  ((X = Pi1_l (Sum_l A' B') M') \/
  (exists4 u u' v v',
  M = Pair_l (Sum_l A' B') u v /\
  exists A'', e |-- A' -> A'' : s1 /\
  exists B'', A' :: e |-- B' -> B'' : s2 /\
  e |-- M -> Pair_l (Sum_l A'' B'') u' v' : Sum_l A' B' /\
  X = u')).
Proof.
  intros.
  pose (generation_pi1 H) ; destruct_exists.
  exists a b ; repeat split ; auto.
  exists a0 b0 c d ; repeat split ; auto.
  intuition.
  destruct_exists.
  exists x.
  intuition.

  destruct_exists.
  exists (Pair_l (Sum_l x x0) b1 d0).
  intuition.
  destruct (validity H7) ; destruct_exists ; try discriminate.
  apply tposr_conv with (Sum_l a0 b0) b2 ; auto with coc.
  apply tposr_coerce_sym.
  eapply tposr_coerce_sum with c d ; eauto with coc ecoc.
  pose (generation_sum H9) ; destruct_exists.
  assert (Heq:=unique_sort (coerce_refl_r H2) H10).
  subst b3.
  assert(a :: e |-- b0 -> a4 : b4).
  apply tposr_coerce_env with (a0 :: e) ; eauto with coc ecoc.
  assert (Heq:=unique_sort H6 H11).
  subst b4.
  rewrite (equiv_eq_sort H14).
  assumption.
  right ; intuition.
  exists a1 b1 c0 d0 ; intuition.
  exists x ; intuition.
  exists x0 ; intuition.
Qed.

Lemma generation_pi2_alt :
  forall e T M X C, e |-- Pi2_l T M -> X : C ->
  exists2 A B, T = Sum_l A B /\ equiv e C (lsubst (Pi1_l T M) B) /\
  exists4 A' B' s1 s2, 
  e |-- A >-> A' : s1 /\ A :: e |-- B >-> B' : s2 /\
  exists M', e |-- M -> M' : Sum_l A B /\
  ((X = Pi2_l (Sum_l A' B') M') \/
  (exists4 u u' v v',
  M = Pair_l (Sum_l A' B') u v /\
  exists A'', e |-- A' -> A'' : s1 /\
  exists B'', A' :: e |-- B' -> B'' : s2 /\
  e |-- M -> Pair_l (Sum_l A'' B'') u' v' : Sum_l A' B' /\
  X = v')).
Proof.
  intros.
  pose (generation_pi2 H) ; destruct_exists.
  exists a b ; repeat split ; auto.
  exists a0 b0 c d ; repeat split ; auto.
  intuition.
  destruct_exists.
  exists x.
  intuition.

  destruct_exists.
  exists (Pair_l (Sum_l x x0) b1 d0).
  intuition.
  destruct (validity H7) ; destruct_exists ; try discriminate.
  apply tposr_conv with (Sum_l a0 b0) b2 ; auto with coc.
  apply tposr_coerce_sym.
  eapply tposr_coerce_sum with c d ; eauto with coc ecoc.
  pose (generation_sum H9) ; destruct_exists.
  assert (Heq:=unique_sort (coerce_refl_r H2) H10).
  subst b3.
  assert(a :: e |-- b0 -> a4 : b4).
  apply tposr_coerce_env with (a0 :: e) ; eauto with coc ecoc.
  assert (Heq:=unique_sort H6 H11).
  subst b4.
  rewrite (equiv_eq_sort H14).
  assumption.
  right ; intuition.
  exists a1 b1 c0 d0 ; intuition.
  exists x ; intuition.
  exists x0 ; intuition.
Qed.

Lemma substitution_coerce_eq : forall e u v s, e |-- u ~= v : s ->
  forall U V s', Srt_l s :: e |-- U >-> V : s' -> e |-- lsubst u U >-> lsubst v V : s'.
Proof.
  intros.
  destruct (tposr_eq_cr H) ; destruct_exists.
  apply tposr_coerce_trans with (lsubst x U).
  apply substitution_coerce_tposrp with s ; auto with coc.
  apply tposr_coerce_conv ; apply tposr_eq_tposr.
  apply (coerce_refl_l H0).
  apply tposr_coerce_sym.
  apply substitution_coerce_tposrp with s ; auto with coc.
Qed. 

Lemma generation_sump : forall e t u T, e |-- t -+> u : T -> 
  forall U V, t = Sum_l U V ->
  exists2 U' V',
  exists s1 : sort,
  exists s2 : sort, u = Sum_l U' V' /\ e |-- U -+> U' : s1 /\ U :: e |-- V -+> V' : s2.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  
  subst.
  pose (generation_sum H) ; destruct_exists.
  subst.
  exists a a0 ; exists b ; exists b0 ; auto with coc ecoc.
  destruct (IHtposrp1 U V) ; auto.
  destruct_exists.
  subst.
  destruct (IHtposrp2 a b) ; auto.
  destruct_exists.
  exists a0 b0 ; exists x1 ; exists x2.
  intuition ; auto with coc ecoc.
  apply tposrp_trans with a ; auto with coc.
  rewrite <- (unique_sort (tposrp_refl_r H3) (tposrp_refl_l H2)) ; auto.
  assert(coerce_in_env (a :: e) (U :: e)).
  apply coerce_env_hd with x.
  eauto with coc ecoc.
  assert(U :: e |-- b -+> b0 : x2).
  apply tposrp_coerce_env with (a :: e) ; auto with coc.
  apply tposrp_trans with b ; auto with coc.
  rewrite <- (unique_sort (tposrp_refl_r H4) (tposrp_refl_l H7)) ; auto.
Qed.

Lemma generation_tposrp_sum : forall e t u T, e |-- t -+> u : T -> 
  forall U V, t = Sum_l U V -> forall U' V', u = Sum_l U' V' ->
  exists s1 : sort,
  exists s2 : sort, e |-- U -+> U' : s1 /\ U :: e |-- V -+> V' : s2.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  
  subst.
  pose (generation_sum H) ; destruct_exists.
  subst.
  inversion H3 ; subst.
  exists b ; exists b0 ; auto with coc ecoc.

  subst.
  destruct (generation_sump H (refl_equal (Sum_l U V))) ; destruct_exists.
  
  destruct (IHtposrp1 U V (refl_equal (Sum_l U V)) a b) ; auto.
  destruct_exists.
  subst.
  elim IHtposrp2 with a b U' V' ; intros ; auto.
  destruct_exists.
  exists x1 ; exists x2.
  intuition ; auto with coc ecoc.
  apply tposrp_trans with a ; auto with coc.
  rewrite (unique_sort (tposrp_refl_r H4) (tposrp_refl_l H1)) ; auto.
  assert(coerce_in_env (a :: e) (U :: e)).
  apply coerce_env_hd with x.
  eauto with coc ecoc.
  assert(U :: e |-- b -+> V' : x4).
  apply tposrp_coerce_env with (a :: e) ; auto with coc.
  apply tposrp_trans with b ; auto with coc.
  rewrite (unique_sort (tposrp_refl_r H5) (tposrp_refl_l H8)) ; auto.
Qed.

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
  apply tposrp_tposr ; apply refl_l with x0; auto.
  apply tposrp_tposr ; apply refl_l with x ; auto.  
  rewrite <- H3.
  apply tposrp_tposr ; apply refl_l with x0; auto.
  apply tposrp_tposr ; apply refl_l with x; auto.

  (* Abs *)
  destruct N ; try (simpl in H1 ; try discriminate) ; intros.
  pose (generation_lambda H).
  pose (generation_lambda H0).
  destruct_exists.
  subst.
  inversion H1.
  subst.
  assert(tposr_term G M1 (Srt_l b2)) by eauto with coc ecoc.
  assert(tposr_term G N1 (Srt_l b)) by eauto with coc ecoc.

  pose (IHM1 _ _ _ _ H6 H13 H10) ; destruct_exists.
  assert(conv_in_env (M1 :: G) (x :: G)) by eauto with coc ecoc.
  assert(conv_in_env (N1 :: G) (x :: G)) by eauto with coc ecoc.
  assert(tposr_term (x :: G) M2 a4) by eauto with coc ecoc.
  assert(tposr_term (x :: G) N2 a1) by eauto with coc ecoc.

  pose (IHM2 _ _ _ _ H20 H21 H12) ; destruct_exists.

  destruct (tposrp_uniqueness_of_types H23 H22) ; destruct H26.
  subst.
  elim (tposr_not_kind (refl_l H5)).

  assert(x :: G |-- a1 -> b1 : b0).
  apply conv_env with (N1 :: G) ; auto with coc.
  assert(Heq:= (unique_sort (refl_l H27) (coerce_refl_l H26))).
  subst.

  assert(equiv_sort G (Prod_l N1 a1) (Prod_l M1 a4) x1).
  unfold equiv_sort.
  apply tposr_coerce_prod with b ; auto with coc.
  apply tposr_coerce_conv.
  apply tposr_eq_trans with x ; auto with coc.
  eauto with coc.
  eauto with coc.
  apply coerce_conv_env with (x :: G) ; auto with coc.
  apply conv_env with (x :: G) ; auto with coc.
  eauto with coc.

  apply conv_env with (x :: G) ; auto with coc.
  apply (coerce_refl_r H26).
  
  assert(equiv_sort G B (Prod_l M1 a4) x1).
  unfold equiv_sort ; apply tposr_coerce_trans with (Prod_l N1 a1) ; auto with coc.

  assert(Heq:=unique_sort (coerce_refl_r H28) (coerce_refl_r H11)).
  subst.
  assert(equiv_sort G A (Prod_l N1 a1) b3).
  unfold equiv_sort ; apply tposr_coerce_trans with (Prod_l M1 a4) ; auto with coc.

  exists (Abs_l x x0).
  assert(G |-- Abs_l M1 M2 -+> Abs_l x x0 : A ).
  apply tposrp_conv with (Prod_l M1 a4) b3 ; auto with coc ecoc.
  apply tposrp_abs with b b4 b3 ; auto with coc ecoc.
  apply tposrp_conv_env with (x :: G) ; eauto with coc ecoc.

  assert(G |-- Abs_l N1 N2 -+> Abs_l x x0 : A ).
  apply tposrp_conv with (Prod_l N1 a1) b3 ; auto with coc ecoc.
  apply tposrp_abs with b b1 b3 ; auto with coc ecoc.
  apply tposrp_conv_env with (x :: G) ; eauto with coc ecoc.

  assert(G |-- A >-> B : b3).
  apply tposr_coerce_trans with (Prod_l N1 a1) ; auto with coc.
  
  intuition ; auto with coc.
  apply tposrp_conv with A b3 ; eauto with coc ecoc.
  apply tposrp_conv with A b3 ; eauto with coc ecoc.

  (* App *)
  destruct N ; try (simpl in H1 ; try discriminate).
  pose (generation_app2 H).
  pose (generation_app2 H0).
  destruct_exists.
  inversion H1 ; subst.
  
  assert(tposr_term G M2 (Prod_l a2 M1)) by eauto with coc ecoc.
  assert(tposr_term G N2 (Prod_l a N1)) by eauto with coc ecoc.
  pose (IHM2 _ _ _ _ H14 H17 H15) ; destruct_exists.
  assert(tposr_term G M3 a2) by eauto with coc ecoc.
  assert(tposr_term G N3 a) by eauto with coc ecoc.
  pose (IHM3 _ _ _ _ H22 H23 H16) ; destruct_exists.
  
  subst.

  pose (tposrp_uniqueness_of_types H18 H19).
  destruct e ; destruct_exists.
  unfold eq_kind in H28 ; intuition ; try discriminate.
  pose (injectivity_of_pi_coerce H28) ; destruct_exists.

  assert(G |-- lsubst N3 N1 >-> lsubst M3 M1 : x3).
  apply tposr_coerce_trans with (lsubst x2 N1).
  apply substitution_coerce_tposrp with a ; eauto with coc ecoc.
  apply tposr_coerce_sym.
  apply substitution_coerce_tposrp with a ; eauto with coc ecoc.

  assert (b3 = x3) by apply (unique_sort (coerce_refl_r H12) (coerce_refl_r H31)).
  assert(b0 = x3) by apply (unique_sort (coerce_refl_r H7) (coerce_refl_l H31)).
  subst.

  exists (App_l M1 x1 x2).
  assert(G |-- A >-> B : x3).
  apply tposr_coerce_trans with (lsubst M3 M1) ; auto with coc.
  apply tposr_coerce_trans with (lsubst N3 N1) ; auto with coc.
  
  assert(G |-- App_l M1 M2 M3 -+> App_l M1 x1 x2 : A).
  apply tposrp_conv with (lsubst M3 M1) x3 ; auto with coc.
  apply tposrp_app with a2 b2 c0 x3 ; auto with coc.
  apply coerce_coerce_env with (a :: G) ; eauto with coc ecoc.

  assert(G |-- App_l N1 N2 N3 -+> App_l M1 x1 x2 : B).
  apply tposrp_conv with (lsubst N3 N1) x3 ; auto with coc.
  apply tposrp_app with a b c x3 ; auto with coc.
  clear H8 ; clear H13.
  intuition ; auto with coc.
  apply tposrp_conv with A x3 ; auto.
  apply tposrp_conv with B x3 ; auto with coc.

  (* Pair *)
  destruct N ; try (simpl in H1 ; try discriminate).
  pose (generation_pair H).
  pose (generation_pair H0).
  destruct_exists.
  subst.
  inversion H1.
  unfold equiv_sort in H17, H10.
  destruct (IHM1 G (Sum_l a a0) x2 x1) ; eauto with coc.
  simpl ; subst ; auto.
  rewrite H3 ; rewrite H9 ; auto.
  destruct (IHM2 G N2 a1 a) ; eauto with coc.
  destruct (IHM3 G N3 (lsubst M2 a2) (lsubst N2 a0)) ; eauto with coc.
  destruct_exists.
  pose (generation_sump H2).
  destruct (e a1 a2) ; auto.
  clear e.
  destruct_exists.
  subst x.
  exists (Pair_l (Sum_l a3 b3) x0 x7).

  assert(G |-- Sum_l a a0 >-> Sum_l a1 a2 : x1).
  apply tposr_coerce_trans with (Sum_l a3 b3) ; auto with coc.
  pose (injectivity_of_sum_coerce H30) ; destruct_exists.
  
  assert(Heq:= unique_sort (refl_l H11)  (coerce_refl_r H33)).
  subst a4.
  assert(Heq:= unique_sort (refl_l H4)  (coerce_refl_l H33)).
  subst c1.
  assert(a :: G |-- a2 -> b2 : c2).
  apply tposr_coerce_env with (a1 :: G) ; eauto with coc ecoc.
  assert(Heq:= unique_sort H36  (coerce_refl_r H34)).
  subst b4.
  assert(Heq:= unique_sort H5 (coerce_refl_l H34)).
  subst c2.
  assert (Heq:=sum_sort_functional H13 H35).
  subst x2.
  assert(Heq:= unique_sort (tposrp_refl_l H31) H11).
  subst x8.
  assert(Heq:= unique_sort (tposrp_refl_l H32) H12).
  subst x9.
   
  assert(G |-- Pair_l (Sum_l a1 a2) M2 M3 -+> Pair_l (Sum_l a3 b3) x0 x7 : A).
  apply tposrp_conv with (Sum_l a1 a2) x1 ; auto with coc.
  apply tposrp_pair with c c0 x1 ; auto with coc.

  assert(G |-- Pair_l (Sum_l a a0) N2 N3 -+> Pair_l (Sum_l a3 b3) x0 x7 : B).
  elim (generation_tposrp_sum H29) with a a0 a3 b3 ; auto ; intros.
  destruct_exists.
  apply tposrp_conv with (Sum_l a a0) x1 ; auto with coc.
  apply tposrp_pair with c c0 x1 ; auto with coc.
  rewrite <- (unique_sort (tposrp_refl_l H38) (coerce_refl_l H33)) ; auto.
  rewrite (unique_sort (coerce_refl_l H34) (tposrp_refl_l H39)) ; auto.

  assert(G |-- A >-> B : x1).
  apply tposr_coerce_trans with (Sum_l a1 a2) ; auto.
  apply tposr_coerce_trans with (Sum_l a3 b3) ; auto with coc.
  apply tposr_coerce_trans with (Sum_l a a0) ; auto with coc.
  intuition.
  apply tposrp_conv with A x1 ; auto with coc.
  apply tposrp_conv with B x1 ; auto with coc.

  (* Prod *)
  pose (generation_prod H) ; destruct_exists.
  subst.
  destruct N ; try discriminate.
  pose (generation_prod H0) ; destruct_exists.
  inversion H1.
  assert(tposr_term G M1 b) by eauto with coc ecoc.
  assert(tposr_term G N1 b1) by eauto with coc ecoc.
  pose (IHM1 _ _ _ _ H9 H12 H10) ; destruct_exists.
  assert(G |-- M1 >-> N1 : b).
  apply tposr_coerce_trans with x0 ; auto with coc.

  assert(tposr_term (M1 :: G) M2 b0) by eauto with coc ecoc.
  assert(M1 :: G |-- N2 -> a2 : b2).
  apply tposr_coerce_env with (N1 :: G) ; eauto with coc ecoc. 
  assert(tposr_term (M1 :: G) N2 b2) by eauto with coc ecoc.
  pose (IHM2 _ _ _ _ H18 H20 H11) ; destruct_exists.
  exists (Prod_l x0 x1).

  assert(G |-- Prod_l M1 M2 -+> Prod_l x0 x1 : A).
  apply tposrp_equiv_l with b0 ; auto with coc.
  subst x.
  apply tposrp_prod with b ; auto with coc.
  
  assert(G |-- Prod_l N1 N2 -+> Prod_l x0 x1 : B).
  apply tposrp_equiv_l with b2 ; auto with coc.
  apply tposrp_prod with b ; auto with coc.
  apply tposrp_coerce_env with (M1 :: G) ; eauto with coc ecoc.

  assert(equiv G A B).
  pose (tposrp_uniqueness_of_types H21 H22).
  pose (wf_tposr H0).
  pose(equiv_sort_strenghten e t).
  apply equiv_trans with b0 ; auto.
  apply equiv_trans with b2 ; auto.

  intuition.
  apply tposrp_equiv_l with A ; auto.
  apply tposrp_equiv_l with B ; auto with coc.

  (* Sum *)
  pose (generation_sum H) ; destruct_exists.
  subst.
  destruct N ; try discriminate.
  pose (generation_sum H0) ; destruct_exists.
  inversion H1.
  assert(tposr_term G M1 b) by eauto with coc ecoc.
  assert(tposr_term G N1 b1) by eauto with coc ecoc.
  pose (IHM1 _ _ _ _ H11 H14 H12) ; destruct_exists.

  assert(G |-- M1 >-> N1 : b).
  apply tposr_coerce_trans with x2 ; auto with coc.

  assert(tposr_term (M1 :: G) M2 b0) by eauto with coc ecoc.
  assert(M1 :: G |-- N2 -> a2 : b2).
  apply tposr_coerce_env with (N1 :: G) ; eauto with coc ecoc. 
  assert(tposr_term (M1 :: G) N2 b2) by eauto with coc ecoc.
  pose (IHM2 _ _ _ _ H20 H22 H13) ; destruct_exists.
  exists (Sum_l x2 x3).

  assert(x0 = x1).
  pose (tposrp_uniqueness_of_types H15 H16).
  pose (tposrp_uniqueness_of_types H23 H24).
  assert (Heq:=equiv_eq_sort e).
  subst b1.
  assert(Heq:=equiv_eq_sort e0).
  subst b2.
  apply (sum_sort_functional H8 H4).

  assert(equiv G A B).
  rewrite H27 in H10.
  apply equiv_trans with x1 ; auto with coc.

  assert(G |-- Sum_l M1 M2 -+> Sum_l x2 x3 : A).
  apply tposrp_equiv_l with x1 ; auto with coc.
  subst x.
  apply tposrp_sigma with b b0 ; auto with coc.
  
  assert(G |-- Sum_l N1 N2 -+> Sum_l x2 x3 : B).
  apply tposrp_equiv_l with x0 ; auto with coc.
  apply tposrp_sigma with b b0 ; auto with coc.
  apply tposrp_coerce_env with (M1 :: G) ; eauto with coc ecoc.
  rewrite H27 ; auto.
  
  intuition.
  apply tposrp_equiv_l with A ; auto.
  apply tposrp_equiv_l with B ; auto with coc.

  (* Subset *)
  destruct N ; try discriminate.
  pose (generation_subset H).
  pose (generation_subset H0).
  destruct_exists.
  inversion H1 ; subst.
  assert(tposr_term G M1 set) by eauto with coc ecoc.
  assert(tposr_term G N1 set) by eauto with coc ecoc.
  assert(tposr_term (M1 :: G) M2 prop) by eauto with coc ecoc.

  pose (IHM1 _ _ _ _ H5 H8 H11) ; destruct_exists.

  assert(M1 :: G |-- N2 -> b : prop).
  apply tposr_coerce_env with (N1 :: G) ; auto with coc ecoc.
  apply coerce_env_hd with set ; auto with coc.
  apply tposr_coerce_trans with x ; auto with coc.

  assert(tposr_term (M1 :: G) N2 prop) by eauto with coc ecoc.
  pose (IHM2 _ _ _ _ H10 H18 H12) ; destruct_exists.

  exists (Subset_l x x0).

  assert(G |-- Subset_l M1 M2 -+> Subset_l x x0 : set).
  apply tposrp_subset ; auto with coc.

  assert(G |-- Subset_l N1 N2 -+> Subset_l x x0 : set).
  apply tposrp_subset ; auto with coc.
  apply tposrp_coerce_env with (M1 :: G) ; auto with coc ecoc.
  apply coerce_env_hd with set ; auto with coc.
  apply tposr_coerce_trans with x ; auto with coc.

  intuition ;
  apply tposrp_conv with set kind ; auto with coc.

  (* Pi1 *)
  destruct N ; try discriminate.
  inversion H1.
  pose (generation_pi1_alt H).
  pose (generation_pi1_alt H0).
  destruct_exists.

  assert(tposr_term G M2 (Sum_l a0 b0)) by eauto with coc ecoc.
  assert(tposr_term G N2 (Sum_l a b)) by eauto with coc ecoc.
  pose (IHM2 _ _ _ _ H15 H16 H3) ; destruct_exists.

  pose (tposrp_uniqueness_of_types H17 H18).
  destruct e ; destruct_exists.
  destruct H21 ; try discriminate.
  pose (injectivity_of_sum_coerce H21) ; destruct_exists.
  assert(Heq:=unique_sort (coerce_refl_l H11) (coerce_refl_l H22)).
  subst a3.
  assert(Heq:=unique_sort (coerce_refl_l H12) (coerce_refl_l H23)).
  subst b3.
  assert(Heq:=unique_sort (coerce_refl_l H6) (coerce_refl_r H22)).
  subst c0.
  assert(a :: G |-- b0 >-> b : d0).
  apply coerce_coerce_env with (a0 :: G) ; eauto with coc ecoc.

  assert(Heq:=unique_sort (coerce_refl_l H7) (coerce_refl_r H25)).
  subst d0.

  exists (Pi1_l M1 x3).
  assert(G |-- Pi1_l M1 M2 -+> Pi1_l M1 x3 : A).
  apply tposrp_equiv_l with a0 ; auto with coc.
  subst M1.
  apply tposrp_pi1 with c d x4 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
 
  assert(G |-- Pi1_l N1 N2 -+> Pi1_l M1 x3 : B).
  apply tposrp_equiv_l with a ; auto with coc.
  subst N1 ; subst M1.
  apply tposrp_pi1 with c d x4 ; auto with coc.
  
  clear H9 H14.
  assert(equiv G A B).
  apply equiv_trans with a0 ; auto with coc.
  apply equiv_trans with a ; auto with coc.
  eauto with coc ecoc.

  intuition.
  apply tposrp_equiv_l with A ; auto with coc.
  apply tposrp_equiv_l with B ; auto with coc.

  (* Pi2 *)
  destruct N ; try discriminate.
  inversion H1.
  pose (generation_pi2_alt H).
  pose (generation_pi2_alt H0).
  destruct_exists.

  assert(tposr_term G M2 (Sum_l a0 b0)) by eauto with coc ecoc.
  assert(tposr_term G N2 (Sum_l a b)) by eauto with coc ecoc.
  pose (IHM2 _ _ _ _ H15 H16 H3) ; destruct_exists.

  pose (tposrp_uniqueness_of_types H17 H18).
  destruct e ; destruct_exists.
  destruct H21 ; try discriminate.
  pose (injectivity_of_sum_coerce H21) ; destruct_exists.
  assert(Heq:=unique_sort (coerce_refl_l H11) (coerce_refl_l H22)).
  subst a3.
  assert(Heq:=unique_sort (coerce_refl_l H12) (coerce_refl_l H23)).
  subst b3.
  assert(Heq:=unique_sort (coerce_refl_l H6) (coerce_refl_r H22)).
  subst c0.
  assert(a :: G |-- b0 >-> b : d0).
  apply coerce_coerce_env with (a0 :: G) ; eauto with coc ecoc.

  assert(Heq:=unique_sort (coerce_refl_l H7) (coerce_refl_r H25)).
  subst d0.

  exists (Pi2_l M1 x3).
  assert(G |-- Pi2_l M1 M2 -+> Pi2_l M1 x3 : A).
  apply tposrp_equiv_l with (lsubst (Pi1_l M1 M2) b0) ; auto with coc.
  subst M1.
  apply tposrp_pi2 with c d x4 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
 
  assert(G |-- Pi2_l N1 N2 -+> Pi2_l M1 x3 : B).
  apply tposrp_equiv_l with (lsubst (Pi1_l N1 N2) b) ; auto with coc.
  subst N1 ; subst M1.
  apply tposrp_pi2 with c d x4 ; auto with coc.

  assert(G |-- Pi1_l M1 M2 -+> Pi1_l M1 x3 : a0).
  subst M1.
  apply tposrp_pi1 with c d x4 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.

  assert(G |-- Pi1_l N1 N2 -+> Pi1_l M1 x3 : a).
  subst M1 ; subst N1.
  apply tposrp_pi1 with c d x4 ; auto with coc.

  clear H9 H14.
  assert(equiv G A B).
  apply equiv_trans with (lsubst (Pi1_l M1 M2) b0) ; auto with coc.
  apply equiv_trans with (lsubst (Pi1_l N1 N2) b); auto with coc.
  right ; exists d.
  apply tposr_coerce_trans with (lsubst (Pi1_l M1 x3) b0).
  apply tposr_coerce_conv.
  apply tposrp_tposr_eq.
  change (Srt_l d) with (lsubst (Pi1_l M1 M2) (Srt_l d)).
  apply substitution_tposrp_tposr with a0 ; auto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_coerce_trans with (lsubst (Pi1_l N1 N2) b0) ; auto with coc.
  apply tposr_coerce_sym.
  apply tposr_coerce_conv.
  apply tposrp_tposr_eq.
  change (Srt_l d) with (lsubst (Pi1_l N1 N2) (Srt_l d)).
  apply substitution_tposrp_tposr with a0 ; auto with coc ecoc.
  apply tposrp_conv with a c ; auto with coc.
  eauto with coc ecoc.
  apply substitution_coerce with a0 ; auto with coc ecoc.
  apply tposr_conv with a c ; auto with coc.
  eauto with coc.

  intuition.
  apply tposrp_equiv_l with A ; auto with coc.
  apply tposrp_equiv_l with B ; auto with coc.
Qed.  

Corollary unlab_conv_sorted : forall G A B s t, tposr_term G A (Srt_l s) ->
  tposr_term G B (Srt_l t) -> ( | A | ) = ( | B | ) -> s = t /\ G |-- A ~= B : s.
Proof.
  intros.
  pose (tposr_unlab_conv H H0 H1) ; destruct_exists.
  split.

  pose (tposrp_refl_l H2).
  pose (tposrp_refl_l H3).
  apply (unique_sort t0 t1).

  apply tposr_eq_trans with x ; auto.
  apply tposrp_tposr_eq ; auto.
  apply tposr_eq_sym ; auto.
  apply tposrp_tposr_eq ; auto.
Qed.

Inductive conv_in_env_full : lenv -> lenv -> Prop :=
  | conv_env_trans : forall e f g, conv_in_env_full e f -> conv_in_env_full f g -> conv_in_env_full e g
  | conv_env_in_env : forall e f, conv_in_env e f -> conv_in_env_full e f
  | conv_env_nil : conv_in_env_full nil nil.

Hint Resolve conv_env_in_env conv_env_nil : coc.


Lemma conv_env_full_sym : forall e f, conv_in_env_full e f -> conv_in_env_full f e.
Proof.
  induction 1 ; simpl ; intros ; eauto with coc.
  apply conv_env_trans with f ; auto.
Qed.

Lemma conv_env_full :
  (forall e t u T, e |-- t -> u : T -> 
  forall f, conv_in_env_full e f -> f |-- t -> u : T).
Proof.
  intros.
  induction H0 ; auto.

  apply conv_env with e ; auto with coc.
Qed.

Lemma conv_env_full_cons : forall G D, conv_in_env_full G D -> forall T, tposr_wf (T :: G) ->
  conv_in_env_full (T :: G) (T :: D).
Proof.
  induction 1 ; simpl ; intros.
  apply conv_env_trans with (T :: f) ; eauto with coc.
  apply IHconv_in_env_full2.
  inversion H1.
  apply wf_cons with s.
  apply conv_env_full with e ; auto with coc.

  apply conv_env_in_env ; auto with coc.

  apply conv_env_in_env ; auto with coc.
  inversion H.
  assert(nil |-- T ~= T : s).
  apply tposr_eq_tposr ; eauto with coc.
  apply conv_env_hd with s ; auto with coc.
Qed.


Corollary tposrp_conv_env_full : 
  (forall e t u T, e |-- t -+> u : T -> 
  forall f, conv_in_env_full e f -> f |-- t -+> u : T).
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  apply tposrp_tposr ; eapply conv_env_full ; eauto with coc.
  apply tposrp_trans with X ; auto with coc.
Qed.

Corollary eq_conv_env_full : 
  (forall e t u s, e |-- t ~= u : s -> 
  forall f, conv_in_env_full e f -> f |-- t ~= u : s).
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  apply tposr_eq_tposr ; eapply conv_env_full ; eauto with coc.
  apply tposr_eq_trans with X ; auto with coc.
Qed.

Hint Resolve conv_env_full eq_conv_env_full : ecoc.

Corollary coerce_conv_env_full : 
  (forall e t u s, e |-- t >-> u : s -> 
  forall f, conv_in_env_full e f -> f |-- t >-> u : s).
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  apply tposr_coerce_conv ; eapply eq_conv_env_full ; eauto with coc.

  assert(conv_in_env_full (A' :: e) (A' :: f)) by
  (apply conv_env_full_cons ; auto with coc;
  eauto with coc ecoc).
  assert(conv_in_env_full (A :: e) (A :: f)) by
  (apply conv_env_full_cons ; auto with coc;
  eauto with coc ecoc).
  apply tposr_coerce_prod with s ; eauto with coc ecoc.

  assert(conv_in_env_full (A' :: e) (A' :: f)) by
  (apply conv_env_full_cons ; auto with coc;
  eauto with coc ecoc).
  assert(conv_in_env_full (A :: e) (A :: f)) by
  (apply conv_env_full_cons ; auto with coc;
  eauto with coc ecoc).
  apply tposr_coerce_sum with s s' ; eauto with coc ecoc.

  assert(conv_in_env_full (U :: e) (U :: f)) by
  (apply conv_env_full_cons ; auto with coc;
  eauto with coc ecoc).
  apply tposr_coerce_sub_l ; eauto with coc ecoc.

  assert(conv_in_env_full (U' :: e) (U' :: f)) by
  (apply conv_env_full_cons ; auto with coc ; eauto with coc ecoc).
  apply tposr_coerce_sub_r ; eauto with coc ecoc.
  
  apply tposr_coerce_trans with B ; auto.
Qed.

Lemma unlab_conv_ctx_conv : forall G D, tposr_wf G -> tposr_wf D -> 
  (unlab_ctx D) = (unlab_ctx G) -> conv_in_env_full G D.
Proof.
  induction G ; induction D ; simpl ; intros ; try discriminate ; auto.

  apply conv_env_nil.  

  apply conv_env_trans with (a0 :: G) ; auto with coc.
  apply conv_env_in_env.
  inversion H.
  inversion H0.
  subst.
  assert(tposr_term G a (Srt_l s)) ;  eauto with coc.
  inversion H1.
  pose (conv_env_full_sym (IHG _ (wf_tposr H3) (wf_tposr H6) H7)).
  pose (conv_env_full H6 c).
  assert(tposr_term G a0 (Srt_l s0)) ; eauto with coc.
  pose (unlab_conv_sorted H2 H4 (sym_eq H5)).
  destruct_exists.
  apply conv_env_hd with s ; eauto with coc.
  
  inversion H1 ; subst.
  cut (conv_in_env_full G D).
  intros.
  apply conv_env_full_cons ; auto.
  inversion H ; inversion H0 ; subst.
  apply wf_cons with s0 ; auto.
  apply conv_env_full with D ; auto with coc.
  apply conv_env_full_sym ; auto.

  inversion H ; inversion H0 ; subst ; 
  apply IHG ; eauto with coc.
  apply (wf_tposr H5).
  apply (wf_tposr H8).
Qed.


Corollary unlab_conv_ctx : forall D, tposr_wf D -> forall G M N A, G |-- M -> N : A -> 
 (unlab_ctx D) = (unlab_ctx G) -> D |-- M -> N : A.
Proof.
  intros.
  apply conv_env_full with G ; auto with coc.
  apply unlab_conv_ctx_conv ; auto with coc.
  apply (wf_tposr H0).
Qed.

Corollary eq_unlab_conv_ctx : forall D, tposr_wf D -> forall G M N s, G |-- M ~= N : s -> 
 (unlab_ctx D) = (unlab_ctx G) -> D |-- M ~= N : s.
Proof.
  intros.
  pose (unlab_conv_ctx_conv (wf_tposr (eq_refl_l H0)) H H1).
  apply eq_conv_env_full with G ; auto with coc.
Qed.

Corollary coerce_unlab_conv_ctx : forall D, tposr_wf D -> forall G M N s, G |-- M >-> N : s -> 
 (unlab_ctx D) = (unlab_ctx G) -> D |-- M >-> N : s.
Proof.
  intros.
  pose (unlab_conv_ctx_conv (wf_tposr (coerce_refl_l H0)) H H1).
  apply coerce_conv_env_full with G ; auto with coc.
Qed.

Require Import Lambda.Reduction.
Require Import Lambda.Conv.

Lemma conv_eq : forall t u, conv (|t|) (|u|) ->
  forall e (s : sort), e |-- t -> t : s -> e |-- u -> u : s -> e |-- t ~= u : s.
Proof.
  intros t u H.
  destruct(church_rosser _ _ H). 
  intros ; subst.
  destruct (unlab_lab_red _ H1).
  destruct (unlab_lab_red _ H0).
  destruct_exists.
  subst x.
  pose (lred_par_lred _ _ H7).
  pose (lred_par_lred _ _ H6).

  assert(tposr_term e t s) by eauto with coc ecoc.
  assert(tposr_term e u s) by eauto with coc ecoc.
  pose (subject_reduction_p p0 H4).
  apply tposr_eq_trans with x1.
  auto with coc.

  apply tposr_eq_sym.
  pose (subject_reduction_p p H8).
  apply tposr_eq_trans with x0.
  auto with coc.
  
  assert(tposr_term e x1 s) by eauto with coc ecoc.
  assert(tposr_term e x0 s) by eauto with coc ecoc.
  pose (tposr_unlab_conv H9 H10 H5) ; destruct_exists.
  apply tposr_eq_trans with x ; auto with coc.
Qed.
