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
Require Import Lambda.TPOSR.CtxCoercion.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.Equiv.
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.TypesDepth.
Require Import Lambda.TPOSR.TypesFunctionality.
Require Import Lambda.TPOSR.UniquenessOfTypes.

Require Import Lambda.TPOSR.MaxLemmas.

Set Implicit Arguments.
Implicit Type s : sort.

Lemma tposr_tposr_coerce : forall G M N s, G |-- M -> N : s -> G |-- M >-> N : s.
Proof.
  auto with coc.
Qed.

Lemma tposrd_tposr_coerce : forall G M N s n, G |-- M -> N : s [n] -> G |-- M >-> N : s.
Proof.
  intros.
  pose (fromd H) ; auto with coc.
Qed.

Hint Resolve tposrd_tposr_coerce : ecoc.

Lemma equiv_coerce_in_env : forall G M N s, G |-- M -> M : s -> equiv G M N -> 
  coerce_in_env (M :: G) (N :: G).
Proof.
  intros.
  destruct H0.
  destruct H0 ; subst.
  elim (tposr_not_kind H).
  destruct H0.
  apply coerce_env_hd with x.
  auto with coc.
Qed.

Theorem church_rosser_depth : forall n m,
  forall G M N A, G |-- M -> N : A [n] ->
  forall P B, G |-- M -> P : B [m] ->
  exists Q, 
  (G |-- N -> Q : A /\
  G |-- N -> Q : B /\
  G |-- P -> Q : A /\
  G |-- P -> Q : B).
Proof.
  intros n.
  pattern n.
  apply wf_lt_induction_type.
  intros x IH m.

  intros G M N A Hl.
  pose (Hl2 := fromd Hl).
  inversion Hl.
  rewrite <- H2 in Hl2.
  rewrite <- H3 in Hl2.

  (* Var *)
  intros P B Hr.
  pose (Hr2 := fromd Hr).
  pose (generation_var Hr2) ; destruct_exists.
  rewrite H6 in Hr2.
  rewrite H6.
  exists (Ref_l n0) ; intuition.
  
  (* Set *)
  intros P B Hr.
  pose (generation_sort (fromd Hr)) ; destruct_exists.
  rewrite H5.
  rewrite H5 in Hr.
  rewrite H6.
  rewrite H6 in Hr.
  pose (fromd Hr).
  exists (Srt_l set) ; intuition.

  (* Prop *)
  intros P B Hr.
  pose (generation_sort (fromd Hr)) ; destruct_exists.
  rewrite H5.
  rewrite H5 in Hr.
  rewrite H6.
  rewrite H6 in Hr.
  pose (fromd Hr).
  exists (Srt_l prop) ; intuition.

  (* Prod *)
  rewrite <- H2 in Hl2.
  rewrite <- H3 in Hl2.
  rewrite <- H4 in Hl2.
  intros P B0 Hr.
  pose (generation_prod_depth Hr) ; destruct_exists.
  rewrite H10.

  assert(n0 < x) ; try rewrite <- H5 ; auto with arith.
  pose (IH _ H12 _ _ _ _ _ H _ _ H6) ; destruct_exists.
  assert(m0 < x) ; try rewrite <- H5 ; auto with arith.
  pose (IH _ H17 _ _ _ _ _ H0 _ _ H8) ; destruct_exists.
  assert(conv_in_env (A0 :: G) (A' :: G)).
  apply conv_env_hd with s1 ; auto with coc.
  apply tposr_eq_tposr ; apply (fromd H).
  assert(conv_in_env (A0 :: G) (a :: G)).
  apply conv_env_hd with b ; auto with coc.
  apply tposr_eq_tposr ; apply (fromd H6).

  exists (Prod_l x0 x1) ; intuition ; try apply tposr_prod with s1 ; 
  try apply tposr_prod with b ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_equiv_r with (Srt_l b0) ; auto.
  apply tposr_prod with s1 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_equiv_r with (Srt_l b0) ; auto.
  apply tposr_prod with s1 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.

  (* Abs *)
  intros P B0 Hr.
  pose (generation_lambda_depth Hr) ; destruct_exists.
  assert(n0 < x) ; try rewrite <- H6 ; auto with arith.
  pose (IH _ H15 _ _ _ _ _ H _ _ H7) ; destruct_exists.
  assert(p < x) ; try rewrite <- H6 ; auto with arith.
  pose (IH _ H20 _ _ _ _ _ H1 _ _ H9) ; destruct_exists.
  assert(conv_in_env (A0 :: G) (A' :: G)).
  apply conv_env_hd with s1 ; auto with coc.
  apply tposr_eq_tposr ; apply (fromd H).
  assert(conv_in_env (A0 :: G) (a :: G)).
  apply conv_env_hd with b ; auto with coc.
  apply tposr_eq_tposr ; apply (fromd H7).
  rewrite H13.
  subst.

  pose (tposr_uniqueness_of_types Hl2 (fromd Hr)).
  destruct e.
  destruct H2 ; try discriminate.
  destruct H2.
  
  assert(x = b0).
  apply (unique_sort (coerce_refl_r H2) (coerce_refl_l H14)).

  assert(x = s2).
  assert(G |-- Prod_l A0 B -> Prod_l A0 B : s2).
  apply tposr_prod with s1 ; auto with coc.
  apply (refl_l (fromd H)).
  apply (refl_l (fromd H0)).
  apply (unique_sort (coerce_refl_l H2) (refl_l H4)).
  subst.
  rewrite <- H4 in H0.
  clear H4 s2.

  assert(s1 = b).
  apply (unique_sort (refl_l H16) (refl_l H17)).
  subst.

  assert(G |-- Abs_l A' M' -> Abs_l x0 x1 : Prod_l A0 B).
  apply tposr_conv with (Prod_l A' B) b0 ; auto with coc.
  apply tposr_abs with b B' b0 ; auto with coc ecoc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply (fromd H0).
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_coerce_prod with b ; auto with coc.
  eauto with ecoc.
  apply (refl_l (fromd H)).
  apply (refl_r (fromd H)).
  pose (refl_l (fromd H0)) ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  pose (refl_l (fromd H0)) ; auto with coc.
  pose (refl_l (fromd H0)) ; auto with coc.

  assert(G |-- Abs_l a a0 -> Abs_l x0 x1 : Prod_l A0 B).
  apply tposr_conv with (Prod_l a B) b0 ; auto with coc.
  apply tposr_abs with b B' b0 ; auto with coc ecoc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply (fromd H0).
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_coerce_prod with b ; auto with coc.
  eauto with ecoc.
  apply (refl_l (fromd H)).
  apply (refl_r (fromd H7)).
  pose (refl_l (fromd H0)) ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  pose (refl_l (fromd H0)) ; auto with coc.
  pose (refl_l (fromd H0)) ; auto with coc.

  exists (Abs_l x0 x1) ; intuition ; auto with coc.
  apply tposr_conv with (Prod_l A0 B) b0 ; auto.
  apply tposr_conv with (Prod_l A0 B) b0 ; auto.

  (* App *)
  intros P B0 Hr.
  pose (generation_app_depth Hr) ; destruct_exists.

  assert(q < x) ; try rewrite <- H7 ; auto with arith.
  pose (IH _ H15 _ _ _ _ _ H2 _ _ H11) ; destruct_exists.
  pose (uniqueness_of_types (toq H2) (toq H11)).
  assert(c = s1).
  destruct e0 ; unfold eq_kind in H20 ; destruct_exists.
  rewrite H21 in H8 ; clear H21.
  elim (tposr_not_kind (fromd H8)).
  rewrite (unique_sort (fromd H8) (coerce_refl_r H20)).
  apply (unique_sort (coerce_refl_l H20) (fromd H)).
  
  assert(coerce_in_env (a :: G) (A0 :: G)).
  apply equiv_coerce_in_env with c ; auto with coc.
  apply (refl_l (fromd H8)).

  assert(coerce_in_env (A0 :: G) (a :: G)).
  apply equiv_coerce_in_env with s1 ; auto with coc.
  apply (refl_l (fromd H)).
  
  assert(tposr_wf (A0 :: G)).
  apply (wf_tposr (coerce_refl_l H0)).

  assert(tposr_wf (a :: G)).
  apply (wf_tposr (coerce_refl_l H10)).

  assert(A0 :: G |-- B >-> a0 : b0).
  apply coerce_coerce_env with (a :: G) ; auto with coc.

  assert(a :: G |-- B >-> B' : s2).
  apply coerce_coerce_env with (A0 :: G) ; auto with coc.

  assert(b0 = s2).
  pose (coerce_refl_l H25).
  pose (coerce_refl_l H0).
  apply (unique_sort t t0).
  rewrite H20 in H8.
  rewrite H27 in H10.
  rewrite H27 in H25.
  rewrite H27 in H13.
  clear H27 b0.

(*  assert(n0 < x) by (rewrite <- H7 ; auto with arith). 
  pose (tod H25) ; destruct_exists.
  pose (IH _ H27 _ _ _ _ _ H _ _ H2) ; destruct_exists.

  assert(G |-- lsubst x0 x2 ~= lsubst N0 B : s2).
  apply tposr_eq_sym.
  apply tposr_eq_trans with (lsubst a1 a0).
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst N0 (Srt_l s2)).
  apply substitution with A0 ; auto with coc.
  pose (refl_r (fromd H12)).
  pose (refl_l H19).
  pose (tposr_uniqueness_of_types t t0).
  apply tposr_equiv_l with a ; auto with coc.
  apply (fromd H12).

  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst a1 (Srt_l s2)).
  apply substitution with A0 ; auto with coc.*)

  assert(HeqB: equiv G B0 (lsubst N0 B)).
  right ; exists s2 ; assumption.

  destruct H14 ; destruct_exists.

  (* App, App *)
  rewrite H28.
  assert(p < x) ; try rewrite <- H7 ; auto with arith.
  pose (IH _ H29 _ _ _ _ _ H1 _ _ H14) ; destruct_exists.

  exists (App_l B x1 x0).

  assert(G |-- App_l B' M' N' -> App_l B x1 x0 : lsubst N0 B).
  apply tposr_conv with (lsubst N' B') s2 ; auto with coc.
  apply tposr_app with A0 A' s1 s2 ; auto with coc.
  apply (fromd H).
  apply tposr_conv with (Prod_l A0 B) s2 ; auto with coc.
  assert(G |-- A0 -> A0 : s1).
  apply (refl_l (fromd H)).
  assert(G |-- A0 >-> A0 : s1).
  auto with coc.
  apply tposr_coerce_prod with s1 ; auto with coc.
  apply (coerce_refl_l H25).
  apply (coerce_refl_r H0).
  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with A0 ; auto with coc.
  apply (fromd H2).

  assert(G |-- App_l a0 a2 a1 -> App_l B x1 x0 : lsubst N0 B).
  apply tposr_conv with (lsubst a1 a0) s2 ; auto with coc.
  apply tposr_app with A0 A' s1 s2 ; auto with coc.
  apply (fromd H).
  apply tposr_conv with (Prod_l A0 B) s2 ; auto with coc.

  assert(G |-- A0 -> A0 : s1).
  apply (refl_l (fromd H)).
  assert(G |-- A0 >-> A0 : s1).
  auto with coc.
  apply tposr_coerce_prod with s1 ; auto with coc.
  apply (coerce_refl_l H25).
  apply (coerce_refl_r H25).
  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with a ; auto with coc.
  apply (fromd H11).

  intuition ; auto with coc.
  apply tposr_equiv_r with (lsubst N0 B) ; auto with coc.
  apply tposr_equiv_r with (lsubst N0 B) ; auto with coc.

  (* App, Beta *)
  rewrite H29.
  rewrite H14 in H1.
  pose (generation_lambda_depth H1) ; destruct_exists.
  assert(c2 < x).
  rewrite <- H7 ; auto with arith.
  apply lt_trans with p ; auto with arith.
  pose (IH _ H38 _ _ _ _ _ H32 _ _ H27) ; destruct_exists.

  exists (lsubst x0 x1).

  assert(G |-- a ~= a3 : b2).
  apply tposr_eq_tposr ; auto with coc.
  apply (fromd H30).

  assert (conv_in_env (a :: G) (a3 :: G)).
  apply conv_env_hd with b2 ; auto.

  assert (coerce_in_env (A0 :: G) (a3 :: G)).
  destruct e0.
  destruct H45.
  rewrite H46 in H30.
  elim (tposr_not_kind (fromd H30)).
  destruct H45.
  apply coerce_env_hd with x2.
  apply tposr_coerce_trans with a ; auto with coc.
  destruct (eq_refls H43).
  pose (unique_sort H46 (coerce_refl_r H45)).
  rewrite <- e0 ; auto ; auto with coc.

  assert(G |-- App_l B' M' N' -> lsubst x0 x1 : lsubst N0 B).
  apply tposr_conv with (lsubst N' B') s2 ; auto with coc.

  rewrite H36.
  apply tposr_beta with a3 b2 B' s2 ; auto with coc.
  apply (eq_refl_r H43).
  apply tposr_coerce_env with (A0 :: G) ; auto with coc.
  apply (coerce_refl_r H0).
  apply conv_env with (a :: G) ; auto with coc.
  apply tposr_conv with B s2 ; auto with coc.
  apply tposr_conv_l with a b2 ; auto with coc.

  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with A0 ; auto with coc.
  apply (fromd H2).

  assert(G |-- lsubst a1 b0 -> lsubst x0 x1 : lsubst N0 B).
  apply tposr_conv with (lsubst a1 B') s2 ; auto with coc.

  apply substitution_tposr_tposr with a ; auto with coc.
  apply tposr_conv with B s2 ; auto with coc.

  apply tposr_coerce_sym.   
  apply substitution_tposr_coerce with a ; auto with coc.
  apply (fromd H11).
  
  intuition ; auto with coc.

  apply tposr_equiv_r with (lsubst N0 B) ; auto.
  apply tposr_equiv_r with (lsubst N0 B) ; auto.
Admitted.
(*  (* Beta *)
  intros P B0 Hr.
  pose (generation_app_depth Hr) ; destruct_exists.

  assert(q < x) ; try rewrite <- H7 ; auto with arith.
  pose (IH _ H16 _ _ _ _ _ H2 _ _ H12) ; destruct_exists.
  pose (uniqueness_of_types (toq H2) (toq H12)).
  assert(c = s1).
  destruct e0 ; destruct_exists.
  destruct H21.
  rewrite H22 in H8 ; elim (tposr_not_kind (fromd H8)).
  destruct (coerce_refls H21).
  rewrite <- (unique_sort H22 (fromd H)).
  rewrite <- (unique_sort H23 (fromd H8)).
  reflexivity.

  assert(coerce_in_env (a :: G) (A0 :: G)).
  destruct e0.
  destruct H22.
  rewrite H23 in H8 ; elim (tposr_not_kind (fromd H8)).
  destruct H22.
  apply coerce_env_hd with x1 ; auto with coc.

  assert(A0 :: G |-- B -> a0 : Srt_l b0).
  apply type_coerce_env with (a :: G) ; auto with coc.
  apply (fromd H10).

  assert(a :: G |-- B -> B' : Srt_l s2).
  apply type_coerce_env with (A0 :: G) ; auto with coc.
  apply (fromd H0).

  assert(b0 = s2).
  pose (refl_l H24).
  pose (refl_l (fromd H10)).
  apply (unique_sort t0 t).

  rewrite H21 in H8.
  rewrite H25 in H10.
  rewrite H25 in H14.
  rewrite H25 in H23.
  clear H25 b0.

  assert(m0 < x) by (rewrite <- H7 ; auto with arith). 
  pose (tod H23) ; destruct_exists.
  
  pose (IH _ H25 _ _ _ _ _ H0 _ _ H26) ; destruct_exists.

  assert(G |-- lsubst x0 x2 ~= lsubst N0 B : s2).
  apply tposr_eq_sym.
  apply tposr_eq_trans with (lsubst a1 a0).
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst N0 (Srt_l s2)).
  apply substitution with A0 ; auto with coc.
  pose (refl_r (fromd H12)).
  pose (refl_l H19).
  pose (tposr_uniqueness_of_types t t0).
  apply tposr_equiv_l with a ; auto with coc.
  apply (fromd H12).

  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst a1 (Srt_l s2)).
  apply substitution with A0 ; auto with coc.

  assert(HeqB: equiv G B0 (lsubst N0 B)).
  right ; exists s2 ; assumption.

  destruct H15 ; destruct_exists.

  (* Beta, App *)
  rewrite H33.
  pose (generation_lambda_depth H15) ; destruct_exists.
  assert(p < x).
  rewrite <- H7 ; auto with arith.
  pose (IH _ H42 _ _ _ _ _ H1 _ _ H36) ; destruct_exists.
  assert(n0 < x).
  rewrite <- H7 ; auto with arith.
  pose (IH _ H47 _ _ _ _ _ H _ _ H34) ; destruct_exists.

  assert(G |-- A0 ~= a3 : b2).
  apply tposr_eq_tposr ; auto with coc.
  apply (fromd H34).

  assert (conv_in_env (A0 :: G) (a3 :: G)).
  apply conv_env_hd with b2 ; auto.

  assert (coerce_in_env (a :: G) (a3 :: G)).
  destruct e0.
  destruct H54.
  rewrite H55 in H8 ; elim (tposr_not_kind (fromd H8)).
  destruct H54.
  destruct (coerce_refls H54).
  pose (unique_sort H55 (fromd H34)).
  apply coerce_env_hd with b2 ; auto with coc.
  apply tposr_coerce_trans with A0 ; auto with coc.
  rewrite <- e0 ; auto with coc.

  exists (lsubst x0 x3).

  assert(G |-- App_l a0 a2 a1 -> lsubst x0 x3 : lsubst N0 B).

  apply tposr_conv_l with (lsubst a1 a0) s2 ; auto with coc.
  apply tposr_eq_trans with (lsubst x0 x2) ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst a1 (Srt_l s2)).
  apply substitution with A0 ; auto with coc.
  
  rewrite H40.
  apply tposr_beta with x4 s1 x2 s2 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_conv with B s2 ; auto with coc.
  apply tposr_conv_l with A0 b2 ; auto with coc.

  assert(G |-- lsubst N' M' -> lsubst x0 x3 : lsubst N0 B).

  apply tposr_conv_l with (lsubst N' a0) s2 ; auto with coc.
  apply tposr_eq_trans with (lsubst x0 x2) ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst N' (Srt_l s2)).
  apply substitution with A0 ; auto with coc.
  apply substitution with A0 ; auto with coc.
  apply tposr_conv with B s2 ; auto with coc.

  intuition ; auto with coc.

  apply tposr_equiv_r with (lsubst N0 B) ; auto.
  apply tposr_equiv_r with (lsubst N0 B) ; auto.

  (* Beta, Beta *)
  rewrite H34.
  assert(p < x) ; try rewrite <- H7 ; auto with arith.
  generalize dependent G.
  inversion H15.
  rewrite <- H5.
  rewrite <- H6.
  rewrite <- H4.
  rewrite H0.
  rewrite H1.
  clear H0 H1 A0 M0 H15 H4 H5 H6.
  intros.

  pose (IH _ H35 _ _ _ _ _ H1 _ _ H32) ; destruct_exists.
  
  exists (lsubst x0 x3).

  assert(G |-- lsubst N' M' -> lsubst x0 x3 : lsubst N0 B).
  apply tposr_conv_l with (lsubst N' B') s2 ; auto with coc.
  apply tposr_eq_trans with (lsubst x0 x2) ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst N' (Srt_l s2)).
  apply substitution with a ; auto with coc.
  apply substitution with a ; auto with coc.
  apply tposr_conv with B s2 ; auto with coc.

  assert(G |-- lsubst a1 b0 -> lsubst x0 x3 : lsubst N0 B).
  apply tposr_conv_l with (lsubst a1 B') s2 ; auto with coc.
  apply tposr_eq_trans with (lsubst x0 x2) ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst a1 (Srt_l s2)).
  apply substitution with a ; auto with coc.
  apply substitution with a ; auto with coc.
  apply tposr_conv with B s2 ; auto with coc.

  intuition.

  apply tposr_equiv_r with (lsubst N0 B) ; auto with coc.
  apply tposr_equiv_r with (lsubst N0 B) ; auto with coc.

  (* Conv *)
  intros.
  assert(n0 < x) by (rewrite <- H5 ; auto with arith).
  pose (IH _ H7 _ _ _ _ _ H _ _ H6) ; destruct_exists.
  exists x0 ; intuition.
  apply tposr_conv with A0 s ; auto with coc.
  apply tposr_conv with A0 s ; auto with coc.
 
  (* Subset *)
  intros.
  pose (generation_subset_depth H6) ; destruct_exists.
  rewrite H11.

  assert(n0 < x) by (rewrite <- H5 ; auto with arith).
  assert(m0 < x) by (rewrite <- H5 ; auto with arith).
  pose (IH _ H13 _ _ _ _ _ H _ _ H7) ; destruct_exists.
  pose (IH _ H14 _ _ _ _ _ H0 _ _ H9) ; destruct_exists.

  assert(conv_in_env (A0 :: G) (a :: G)).
  apply conv_env_hd with set ; auto with coc.
  apply tposr_eq_tposr.
  apply (fromd H7).

  assert(conv_in_env (A0 :: G) (A' :: G)).
  apply conv_env_hd with set ; auto with coc.
  apply tposr_eq_tposr.
  apply (fromd H).

  exists (Subset_l x0 x1).
  assert(G |-- Subset_l A' B' -> Subset_l x0 x1 : Srt_l set).
  apply tposr_subset ; auto with coc.
  apply conv_env with (A0 :: G) ; auto.

  assert(G |-- Subset_l a a0 -> Subset_l x0 x1 : Srt_l set).
  apply tposr_subset ; auto with coc.
  apply conv_env with (A0 :: G) ; auto.
  
  intuition ;
  apply tposr_conv with (Srt_l set) kind ; auto with coc.

  (* Sum *)
  rewrite <- H2 in Hl2.
  rewrite <- H3 in Hl2.
  rewrite <- H4 in Hl2.
  intros P B0 Hr.
  pose (generation_sum_depth Hr) ; destruct_exists.
  rewrite H12.

  assert(n0 < x) by (rewrite <- H6 ; auto with arith).
  pose (IH _ H14 _ _ _ _ _ H _ _ H7) ; destruct_exists.
  assert(m0 < x) by (rewrite <- H6 ; auto with arith).
  pose (IH _ H19 _ _ _ _ _ H0 _ _ H9) ; destruct_exists.

  assert(conv_in_env (A0 :: G) (A' :: G)).
  apply conv_env_hd with s1 ; auto with coc.
  apply tposr_eq_tposr ; apply (fromd H).
  assert(conv_in_env (A0 :: G) (a :: G)).
  apply conv_env_hd with b ; auto with coc.
  apply tposr_eq_tposr ; apply (fromd H7).

  exists (Sum_l x1 x2).
  assert(G |-- Sum_l A' B' -> Sum_l x1 x2 : Srt_l s3).
  apply tposr_sum with s1 s2 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  assert(G |-- Sum_l A' B' -> Sum_l x1 x2 : Srt_l x0).
  apply tposr_sum with b b0 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  assert(G |-- Sum_l a a0 -> Sum_l x1 x2 : Srt_l s3).
  apply tposr_sum with s1 s2 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  assert(G |-- Sum_l a a0 -> Sum_l x1 x2 : Srt_l x0).
  apply tposr_sum with b b0 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
   
  intuition ; try apply tposr_equiv_r with (Srt_l x0) ; auto.

  (* Pair *)
  rewrite <- H5 in Hl2.
  rewrite <- H6 in Hl2.
  rewrite <- H7 in Hl2.
  intros P B0 Hr.
  pose (generation_pair_depth Hr) ; destruct_exists.
  rewrite H19.
  inversion H9.
  rewrite <- H22 in H10.
  rewrite <- H22 in H20.
  rewrite <- H22.
  rewrite <- H22 in H12.
  rewrite <- H23 in H12.
  rewrite <- H23 in H17.
  rewrite <- H23 in H20.
  rewrite <- H23.
  rewrite <- H22 in H15.
  clear H22 H23 H9 a a0.

  assert(n0 < x) by (rewrite <- H8 ; auto with arith).
  pose (IH _ H9 _ _ _ _ _ H _ _ H10) ; destruct_exists ; clear H9.
  assert(m0 < x) by (rewrite <- H8 ; auto with arith).
  pose (IH _ H9 _ _ _ _ _ H0 _ _ H12) ; destruct_exists ; clear H9.
  assert(p < x) by (rewrite <- H8 ; auto with arith).
  pose (IH _ H9 _ _ _ _ _ H2 _ _ H15) ; destruct_exists ; clear H9.
  assert(q < x) by (rewrite <- H8 ; auto with arith).
  pose (IH _ H9 _ _ _ _ _ H3 _ _ H17) ; destruct_exists ; clear H9.

  exists (Pair_l (Sum_l x1 x2) x3 x4).

  assert(conv_in_env (A0 :: G) (A' :: G)).
  apply conv_env_hd with s1 ; auto with coc.
  apply tposr_eq_tposr ; apply (fromd H).
  assert(conv_in_env (A0 :: G) (b :: G)).
  apply conv_env_hd with c ; auto with coc.
  apply tposr_eq_tposr ; apply (fromd H10).
  pose (fromd H).
  pose (fromd H0).
  pose (fromd H2).
  pose (fromd H3).
  pose (fromd H10).
  pose (fromd H12).
  pose (fromd H15).
  pose (fromd H17).

  assert(G |-- Pair_l (Sum_l A' B') u' v' -> Pair_l (Sum_l x1 x2) x3 x4 : Sum_l A0 B).
  apply tposr_conv_r with (Sum_l A' B') s3 ; auto with coc ; try apply tposr_pair with s1 s2 s3 ; auto with coc.
  apply tposr_eq_tposr.
  apply tposr_sum with s1 s2 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_conv with A0 s1 ; auto with coc.
  apply tposr_conv_l with (lsubst u B) s2 ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst u (Srt_l s2)).
  apply substitution with A0 ; auto with coc.

  assert(G |-- Pair_l (Sum_l b b0) a1 a2 -> Pair_l (Sum_l x1 x2) x3 x4 : Sum_l A0 B).
  apply tposr_conv_r with (Sum_l b b0) x0 ; auto with coc ; try apply tposr_pair with c c0 x0 ; auto with coc.
  apply tposr_eq_tposr.
  apply tposr_sum with c c0 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_conv with A0 c ; auto with coc.
  apply tposr_conv_l with (lsubst u B) c0 ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l c0) with (lsubst u (Srt_l c0)).
  apply substitution with A0 ; auto with coc.
   
  intuition ; try apply tposr_conv with (Sum_l A0 B) x0 ; auto with coc.

  (* Pi1 *)
  intros.
  pose (generation_pi1_depth H8) ; destruct_exists.
  inversion H13.
  rewrite <- H18 in H15.
  rewrite <- H18 in H16.
  rewrite <- H18.
  rewrite <- H19 in H16.
  clear a1 b1 H19 H18 H13.
  
  assert(n0 < x) by (rewrite <- H7 ; auto with arith).

  pose (fromd H).
  pose (fromd H0).
  pose (fromd H2).
  pose (fromd H9).
  pose (fromd H11).

  destruct H16 ; destruct_exists.

  (* Pi1, Pi1 *)
  rewrite H16 in H9.
  rewrite H17 in H11.
  rewrite H16 in H11.
  rewrite H16 in H19.
  rewrite H18 in H21.
  rewrite H16 in t3.
  rewrite H16 in t4.
  rewrite H17 in t4.
  rewrite H17 in H19.
  rewrite H17 in H24.
  rewrite H16 in H23.
  clear a a0 H16 H17 H9 H11.

  pose (IH _ H13 _ _ _ _ _ H _ _ H22) ; destruct_exists ; clear H13.
  assert(m0 < x) by (rewrite <- H7 ; auto with arith).
  pose (IH _ H13 _ _ _ _ _ H0 _ _ H23) ; destruct_exists ; clear H13.
  clear H24.
  assert(p < x) by (rewrite <- H7 ; auto with arith).
  pose (IH _ H13 _ _ _ _ _ H2 _ _ H19) ; destruct_exists ; clear H13.

  assert(conv_in_env (A :: G) (A' :: G)).
  apply conv_env_hd with s1 ; auto with coc.
  assert(conv_in_env (A :: G) (b :: G)).
  apply conv_env_hd with c ; auto with coc.

  exists (Pi1_l (Sum_l x1 x2) x3).
  assert(G |-- Pi1_l (Sum_l A' B') t' -> Pi1_l (Sum_l x1 x2) x3 : A).
  apply tposr_conv_r with A' s1 ; auto with coc ; try apply tposr_pi1 with s1 s2 s3 ; auto with coc.
  apply conv_env with (A :: G) ; auto with coc.
  apply tposr_conv with (Sum_l A B) s3 ; auto with coc.
  apply tposr_coerce_sum with s1 s2 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply conv_env with (A :: G) ; auto with coc.
  eauto with coc ecoc.
 
  rewrite H21.
  assert(G |-- Pi1_l (Sum_l b b0) b1 -> Pi1_l (Sum_l x1 x2) x3 : A).
  apply tposr_conv_r with b c ; auto with coc ; try apply tposr_pi1 with c c0 x0 ; auto with coc.
  apply conv_env with (A :: G) ; auto with coc.
  apply tposr_conv with (Sum_l A B) x0 ; auto with coc.
  apply tposr_coerce_sum with c c0 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply conv_env with (A :: G) ; auto with coc.
  eauto with coc ecoc.
   
  intuition ; try apply tposr_equiv_r with A ; auto.
  
  (* Pi1, Pi1_red *)
  rewrite H21.
  rewrite H16 in H2.
  pose (generation_pair_depth H22) ; destruct_exists.
  rewrite H33.
  inversion H23.
  rewrite <- H36 in H24.
  rewrite <- H36 in H26.
  rewrite <- H36 in H29.
  rewrite <- H36 in H34.
  rewrite <- H37 in H26.
  rewrite <- H37 in H31.
  rewrite <- H37 in H34.
  clear H36 H37 a3 a4 H23.
  rewrite H16 in H19.
  pose (generation_pair_depth H19) ; destruct_exists.
  inversion H23.
  rewrite <- H47 in H35.
  rewrite <- H47 in H37.
  rewrite <- H47 in H40.
  rewrite <- H47 in H45.
  rewrite <- H48 in H37.
  rewrite <- H48 in H42.
  rewrite <- H48 in H45.
  clear H47 H48 a3 a4 H23.
 
  assert(d1 < x) by (rewrite <- H7 ; apply lt_trans with p ;  auto with arith).
  pose (IH _ H23 _ _ _ _ _ H24 _ _ H35) ; destruct_exists ; clear H23.
  assert(d2 < x) by (rewrite <- H7 ; apply lt_trans with p ; auto with arith).
  pose (IH _ H23 _ _ _ _ _ H26 _ _ H37) ; destruct_exists ; clear H23.
  assert(b5 < x) by (rewrite <- H7 ; apply lt_trans with p ; auto with arith).
  pose (IH _ H23 _ _ _ _ _ H29 _ _ H40) ; destruct_exists ; clear H23.
  assert(b6 < x) by (rewrite <- H7 ; apply lt_trans with p ; auto with arith).
  pose (IH _ H23 _ _ _ _ _ H31 _ _ H42) ; destruct_exists ; clear H23.

  pose (fromd H24).
  assert(conv_in_env (a :: G) (b3 :: G)).
  apply conv_env_hd with c2 ; apply tposr_eq_tposr ; apply t5.
  assert(coerce_in_env (a :: G) (A :: G)).
  apply coerce_env_hd with c ; auto with coc.
  assert(convAA':conv_in_env (A :: G) (A' :: G)).
  apply conv_env_hd with s1 ; auto with coc.

  destruct (coerce_refls H17).
  destruct (coerce_refls H18).
  assert(s1 = c).
  apply (unique_sort t0 H63).
  pose (unique_sort t5 H64).
  assert(s2 = c0).
  pose (fromd H0).
  apply (unique_sort t6 H65).

  exists x5.
  
  assert(G |-- Pi1_l (Sum_l A' B') (Pair_l (Sum_l b3 b4) a5 a6) -> x5 : A).
  apply tposr_conv_r with A' s1 ; auto with coc.
  apply tposr_pi1_red with x3 c2 x4 c3 x1 x6 ; auto with coc.
  apply conv_env with (a :: G) ; auto with coc.
  apply tposr_pair with c2 c3 x1 ; auto with coc.
  apply conv_env with (a :: G) ; auto with coc.
  apply tposr_conv with a c2 ; auto with coc.
  apply tposr_conv with (lsubst a1 a0) c3; auto with coc.
  apply tposr_coerce_conv.
  apply tposr_eq_tposr.
  change (Srt_l c3) with (lsubst a1 (Srt_l c3)).
  apply substitution with a ; auto with coc.
  apply (fromd H26).
  apply (fromd H29).

  apply tposr_coerce_trans with A.
  apply tposr_coerce_sym.
  apply tposr_coerce_conv.
  apply tposr_eq_tposr.
  rewrite e0.
  rewrite <- H67 ; auto.
  apply tposr_coerce_trans with a ; auto with coc.
  rewrite e0 ; auto.

  assert(c0 = c3).
  pose(fromd H26).
  assert(A :: G |-- a0 -> a0 : Srt_l c3).
  apply type_coerce_env with (a :: G) ; auto with coc.
  apply (refl_l t6).
  apply (unique_sort H66 H69).
  rewrite <- H69.
  rewrite <- H68 ; auto.

  apply tposr_coerce_trans with B ; auto with coc.
  apply tposr_coerce_sym.
  apply tposr_coerce_conv.
  apply tposr_eq_tposr.

  apply conv_env with (A :: G) ; auto with coc.

  apply coerce_conv_env with (A :: G) ; auto with coc.
  
  apply tposr_coerce_trans with a0 ; auto with coc.
  rewrite H68.
  assumption.
  rewrite H68.
  rewrite H69.
  apply tposr_coerce_conv.
  apply tposr_eq_tposr ; auto.
  apply type_coerce_env with (a :: G) ; auto with coc.
  apply (fromd H26).
  
  assert(c3 = c0).

  assert(A :: G |-- a0 -> b4 : Srt_l c3).
  apply type_coerce_env with (a :: G) ; auto with coc.
  apply (fromd H26).
  apply (unique_sort H70 H66).
  
  assert(G |-- b1 -> x5 : A).
  inversion H44.
  apply tposr_conv with a c ; auto with coc.

  intuition ; try apply tposr_equiv_r with A ; auto.

  (* Pi1_red *)
  intros.
  rewrite <- H7.
  rewrite H8 in H6.
  clear H8 A''.
  pose (generation_pair_depth H2) ; destruct_exists.
  inversion H8.
  generalize dependent G.
  rewrite <- H23 ; rewrite <- H24.
  inversion H20.
  rewrite <- H0 ; rewrite <- H2.
  rewrite <- H3 ; rewrite <- H4.
  clear a a0 H8 H23 H24 H0 H2 H3 H4 b b0 a1 a2 H20 ; intros.
  clear e H5.

  pose (generation_pi1_depth H10) ; destruct_exists.
  inversion H23.
  generalize dependent G.
  rewrite <- H28.
  rewrite <- H29.
  clear H23 H29 H28 a1 b3.
  intros.

  assert(s1 = c).
  apply (unique_sort (fromd H) (fromd H11)).
  
  assert(s2 = c0).
  apply (unique_sort (fromd H0) (fromd H13)).
  generalize dependent G.
  rewrite <- H23.
  rewrite <- H27.
  intros.
  
  destruct H26 ; destruct_exists.
  
  (* Pi1_red, Pi1 *)
  generalize dependent G.
  rewrite H26.
  rewrite H28.
  rewrite H32.
  rewrite H29.
  clear a a0 a1 P H26 H28 H29 H32.
  intros.
  pose (generation_pair_depth H30).
  destruct_exists.
  inversion H26.
  generalize dependent G.
  rewrite <- H42.
  rewrite <- H43.
  clear H42 H43 H26 a a0.
  rewrite H39.
  rewrite <- H6.
  rewrite <- H7.
  intros.

  assert(b1 < x) by (rewrite <- H9 ; apply lt_trans with p ; auto with arith).
  pose (IH _ H26 _ _ _ _ _ H16 _ _ H35) ; destruct_exists.
  exists x3.
  
  assert(G |-- u' -> x3 : A).
  apply tposr_conv with A0 s1; auto with coc.
  
  assert(conv_in_env (A0 :: G) (b4 :: G)).
  apply conv_env_hd with c4 ; apply tposr_eq_tposr ; apply (fromd H28).

  pose (coerce_refls H3) ; destruct_exists.
  pose (unique_sort H47 (fromd H5)).
  pose (unique_sort H48 (refl_l (fromd H28))).

  assert(G |-- b >-> b4 : c4).
  apply tposr_coerce_trans with A0 ; auto with coc.
  apply tposr_coerce_trans with A ; auto with coc.
  apply tposr_coerce_sym.
  apply tposr_coerce_conv.
  apply tposr_eq_tposr.
  rewrite <- e0.
  rewrite e ; apply (fromd H5).
  rewrite <- e0.
  assumption.
  apply tposr_coerce_conv.
  apply tposr_eq_tposr ; apply (fromd H28).

  pose (coerce_refls H4) ; destruct_exists.
  assert(c2 = s2).
  apply (unique_sort (fromd H20) H50).

  assert(coerce_in_env (A0 :: G) (A :: G)).
  apply coerce_env_hd with s1 ; auto with coc.
  assert(A :: G |-- B -> b5 : Srt_l c5).
  apply type_coerce_env with (A0 :: G) ; auto.
  apply (fromd H32).

  assert(c5 = s2).
  apply (unique_sort H54 H51).
  assert(s1 = c1) ; auto.
  assert(s1 = c4) ; auto.
  generalize dependent G.
  rewrite H52.
  rewrite H55.
  rewrite <- H56.
  rewrite <- H57.
  clear H52 H55 H56 H57.
  intros.

  assert(A :: G |-- b0 >-> b5 : s2).
  apply tposr_coerce_trans with B ; auto.
  apply tposr_coerce_trans with B'' ; auto with coc.
  apply tposr_coerce_sym.
  apply tposr_coerce_conv ; apply tposr_eq_tposr.
  apply (fromd H20).
  apply tposr_coerce_conv ; apply tposr_eq_tposr ; auto.

  assert(G |-- Pi1_l (Sum_l b b0) (Pair_l (Sum_l b4 b5) a1 a2) -> x3 : A).
  apply tposr_conv with b s1 ; try apply (fromd H5) ; auto with coc.
  apply tposr_pi1_red with b4 s1 b5 s2 s3 a2 ; auto with coc.
  apply (refl_r (fromd H28)).
  apply conv_env with (A0 :: G) ; auto with coc.
  apply (refl_r (fromd H32)).
  apply tposr_pair with s1 s2 s3; auto with coc.
  apply (refl_r (fromd H28)).
  apply conv_env with (A0 :: G) ; auto with coc.
  apply (refl_r (fromd H32)).
  apply tposr_conv_l with A0 s1 ; auto.
  apply tposr_eq_tposr ; apply (fromd H28).
  apply tposr_conv_l with (lsubst u B) s2 ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst u (Srt_l s2)).
  apply substitution with A0 ; auto with coc.
  apply (fromd H32).
  apply (fromd H35).
  apply (refl_r (fromd H37)).
  apply coerce_conv_env with (A :: G) ; auto with coc.
  apply conv_env_hd with s1 ; apply tposr_eq_tposr ; apply (fromd H5).
  apply tposr_coerce_sym.
  apply tposr_coerce_conv ; auto with coc.
  apply tposr_eq_tposr ; auto with coc.
  apply (fromd H5).

  intuition ; try apply tposr_equiv_r with A ; auto.

  (* Pi1_red, Pi1_red *)
  rewrite H32.
  generalize dependent G.
  rewrite <- H7.
  clear H23 H27.
  inversion H26.
  rewrite <- H0.
  rewrite <- H2.
  rewrite <- H3.
  rewrite <- H4.
  clear H0 H2 H3 H4 H26.
  intros.
  
  pose (generation_pair_depth H2).
  pose (generation_pair_depth H30).
  destruct_exists.
  generalize dependent G.
  inversion H26 ; inversion H23.
  rewrite <- H0.
  rewrite <- H2.
  rewrite <- H3.
  rewrite <- H4.
  clear H0 H2 H3 H4 H26 H23.
  inversion H52.
  rewrite <- H0.
  rewrite <- H2.
  rewrite <- H3.
  rewrite <- H4.
  clear H0 H2 H3 H4 H52.
  inversion H41.
  rewrite <- H0.
  rewrite <- H2.
  rewrite <- H3.
  rewrite <- H4.
  clear H0 H2 H3 H4 H41.
  intros.

  assert(b1 < x) by (rewrite <- H9 ; apply lt_trans with p ; auto with arith).
  pose (IH _ H23 _ _ _ _ _ H16 _ _ H37) ; destruct_exists.
  exists x4.

  assert(equiv G A A0).
  right ; exists s1 ; auto.

  assert(equiv G B0 A0).
  apply (equiv_trans H25 (equiv_sym H55)).

  intuition ; try apply tposr_equiv_r with A0 ; auto.
  (* Pi2 *)
Admitted.
*)