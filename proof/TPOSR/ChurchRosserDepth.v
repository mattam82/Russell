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

  (* Beta *)
  intros P B0 Hr.
  pose (generation_app_depth Hr) ; destruct_exists.

  assert(q < x) ; try rewrite <- H7 ; auto with arith.
  pose (IH _ H15 _ _ _ _ _ H2 _ _ H11) ; destruct_exists.
  pose (uniqueness_of_types (toq H2) (toq H11)).
  assert(c = s1).
  destruct e0 ; destruct_exists.
  destruct H20.
  rewrite H21 in H8 ; elim (tposr_not_kind (fromd H8)).
  destruct (coerce_refls H20).
  rewrite <- (unique_sort H21 (fromd H)).
  rewrite <- (unique_sort H22 (fromd H8)).
  reflexivity.

  assert(coerce_in_env (a :: G) (A0 :: G)).
  destruct e0.
  destruct H21.
  rewrite H22 in H8 ; elim (tposr_not_kind (fromd H8)).
  destruct H21.
  apply coerce_env_hd with x1 ; auto with coc.

  assert(A0 :: G |-- B >-> a0 : b0).
  apply coerce_coerce_env with (a :: G) ; auto with coc.

  assert(a :: G |-- B -> B' : Srt_l s2).
  apply tposr_coerce_env with (A0 :: G) ; auto with coc.
  apply (fromd H0).

  assert(b0 = s2).
  pose (refl_l H23).
  pose (coerce_refl_l H10).
  apply (unique_sort t0 t).

  rewrite H20 in H8.
  rewrite H24 in H10.
  rewrite H24 in H13.
  rewrite H24 in H22.
  clear H24 b0.

  assert(HeqB: equiv G B0 (lsubst N0 B)).
  right ; exists s2 ; assumption.

  destruct H14 ; destruct_exists.

  (* Beta, App *)
  rewrite H25.
  pose (generation_lambda_depth H14) ; destruct_exists.
  assert(p < x).
  rewrite <- H7 ; auto with arith.
  pose (IH _ H34 _ _ _ _ _ H1 _ _ H28) ; destruct_exists.
  assert(n0 < x).
  rewrite <- H7 ; auto with arith.
  pose (IH _ H39 _ _ _ _ _ H _ _ H26) ; destruct_exists.
  rewrite H32.

  exists (lsubst x0 x1).

  assert(Heqs:=unique_sort H40 H41).
  subst s1.
  subst c.
  subst a2.
  
  assert(G |-- A0 ~= a3 : b2).
  apply tposr_eq_trans with x2 ; auto with coc ecoc.
  apply tposr_eq_trans with A' ; auto with coc ecoc.
  eauto with coc ecoc.

  assert (conv_in_env (A0 :: G) (a3 :: G)).
  apply conv_env_hd with b2 ; auto.

  assert (G |-- A0 >-> a : b2).
  destruct e0.
  destruct H44.
  rewrite H45 in H8 ; elim (tposr_not_kind (fromd H8)).
  destruct H44.
  destruct (coerce_refls H44).
  assert (Heq:=unique_sort H45 (eq_refl_l H20)).
  subst x3.
  assumption.

  assert (coerce_in_env (a :: G) (a3 :: G)).
  apply coerce_env_hd with b2 ; auto with coc.
  apply tposr_coerce_trans with A0 ; auto with coc.
  
  assert(G |-- App_l a0 (Abs_l a3 a4) a1 -> lsubst x0 x1 : lsubst N0 B).

  apply tposr_conv with (lsubst a1 a0) s2 ; auto with coc.
  apply tposr_beta with x2 b2 a0 s2 ; auto with coc.
  apply conv_env with (A0 :: G) ; eauto with coc ecoc.
  apply conv_env with (A0 :: G) ; auto with coc ecoc.
  apply tposr_conv with B s2 ; eauto with coc ecoc.
  apply tposr_conv with A0 b2 ; eauto with coc ecoc.

  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with A0 ; auto with coc ecoc.
  apply tposr_conv with a b2 ; auto with coc ecoc.
  eauto with coc ecoc.

  assert(G |-- lsubst N' M' -> lsubst x0 x1 : lsubst N0 B).

  apply tposr_conv with (lsubst N' a0) s2 ; auto with coc.
  apply substitution_tposr_tposr with A0 ; auto with coc.
  apply tposr_conv with B s2 ; auto with coc.

  apply tposr_coerce_trans with (lsubst x0 a0) ; auto with coc.
  apply substitution_tposr_coerce with A0 ; eauto with coc ecoc.
  apply tposr_coerce_sym.
  apply tposr_coerce_trans with (lsubst a1 a0) ; auto with coc.
  apply substitution_tposr_coerce with A0 ; eauto with coc ecoc.
  apply substitution_tposr_coerce with A0 ; eauto with coc ecoc.

  intuition ; auto with coc.

  apply tposr_equiv_r with (lsubst N0 B) ; auto.
  apply tposr_equiv_r with (lsubst N0 B) ; auto.

  (* Beta, Beta *)
  rewrite H26.
  assert(p < x) ; try rewrite <- H7 ; auto with arith.
  generalize dependent G.
  inversion H14 ; subst.
  intros.

  pose (IH _ H27 _ _ _ _ _ H1 _ _ H24) ; destruct_exists.
  
  exists (lsubst x0 x).

  assert(G |-- lsubst N' M' -> lsubst x0 x : lsubst N0 B).
  apply tposr_conv with (lsubst N' B') s2 ; auto with coc.

  apply substitution_tposr_tposr with a ; auto with coc.
  apply tposr_conv with B s2 ; auto with coc.
  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with a ; eauto with coc ecoc.

  assert(G |-- lsubst a1 b0 -> lsubst x0 x : lsubst N0 B).
  apply tposr_conv with (lsubst a1 B') s2 ; auto with coc.
  apply substitution_tposr_tposr with a ; auto with coc.
  apply tposr_conv with B s2 ; auto with coc.
  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with a ; eauto with coc ecoc.

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
  apply substitution_tposr_tposr with A0 ; auto with coc.

  assert(G |-- Pair_l (Sum_l b b0) a1 a2 -> Pair_l (Sum_l x1 x2) x3 x4 : Sum_l A0 B).
  apply tposr_conv_r with (Sum_l b b0) x0 ; auto with coc ; try apply tposr_pair with c c0 x0 ; auto with coc.
  apply tposr_eq_tposr.
  apply tposr_sum with c c0 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_conv with A0 c ; auto with coc.
  apply tposr_conv_l with (lsubst u B) c0 ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l c0) with (lsubst u (Srt_l c0)).
  apply substitution_tposr_tposr with A0 ; auto with coc.
   
  intuition ; try apply tposr_conv with (Sum_l A0 B) x0 ; auto with coc.

  (* Pi1 *)
  intros.
  pose (generation_pi1_depth H8) ; destruct_exists.
  inversion H9.
  subst A.
  subst A0.
  subst B.
  subst e.

  destruct H13 ; destruct_exists.

  (* Pi1, Pi1 *)
  rewrite H6.
  subst M.
  subst N.

  assert(p < x) by (rewrite <- H7 ; auto with arith).
  pose (IH _ H4 _ _ _ _ _ H2 _ _ H3) ; destruct_exists ; clear H4.

  exists (Pi1_l (Sum_l A' B') x0).

  assert (Heq:=unique_sort (coerce_refl_l H11) (coerce_refl_l H)).
  subst c.
  assert (Heq:=unique_sort (coerce_refl_l H12) (coerce_refl_l H0)).
  subst d.

  assert(G |-- a0 >-> A' : s1).
  apply tposr_coerce_trans with a ; eauto with coc.

  assert(coerce_in_env (a :: G) (A' :: G)).
  apply coerce_env_hd with s1 ; eauto with coc.

  assert(G |-- Pi1_l (Sum_l A' B') t' -> Pi1_l (Sum_l A' B') x0 : a).
  apply tposr_conv with A' s1 ; auto with coc ; try apply tposr_pi1 with s1 s2 s3 ;  auto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply coerce_coerce_env with (a :: G) ; eauto with coc ecoc.
  apply tposr_conv with (Sum_l a b) s3 ; auto with coc.
  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.

  assert(coerce_in_env (a :: G) (a0 :: G)).
  apply coerce_env_hd with s1 ; eauto with coc.

  assert(G |-- Pi1_l (Sum_l a0 b0) a1 -> Pi1_l (Sum_l A' B') x0 : a).
  apply tposr_conv with a0 s1 ; auto with coc ; try apply tposr_pi1 with s1 s2 s3 ;  auto with coc ecoc.
  eauto with coc ecoc.
  apply coerce_coerce_env with (a :: G) ; eauto with coc ecoc.
  apply tposr_conv with (Sum_l a b) s3 ; auto with coc.
  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.

  intuition ; try apply tposr_equiv_r with a ; auto with coc ecoc.
  
  (* Pi1, Pi1_red *)
  subst P.
  subst t.
  subst N.
  subst M.
  assert (Heq:=unique_sort (coerce_refl_l H11) (coerce_refl_l H)).
  subst c.
  assert (Heq:=unique_sort (coerce_refl_l H12) (coerce_refl_l H0)).
  subst d.
 
  assert(p < x) by  (rewrite <- H7 ; auto with arith).  
  pose (IH _ H3 _ _ _ _ _ H2 _ _ H16) ; destruct_exists.
  pose (tod H18).
  destruct_exists.
  pose (generation_pair_depth H20) ; destruct_exists.
  inversion H21.
  subst a4 ; subst a5.
  subst x1.
  assert (Heq:=unique_sort (refl_l (fromd H22)) (refl_r (fromd H6))).
  subst c.
  assert(coerce_in_env (a2 :: G) (a0 :: G)).
  apply coerce_env_hd with s1 ; eauto with coc ecoc.
  assert(a0 :: G |-- a3 -> b5 : c1).
  apply tposr_coerce_env with (a2 :: G) ; eauto with coc ecoc.
  assert (Heq:=unique_sort (refl_r (fromd H14)) (refl_l H33)).
  subst c1.

  pose (generation_pair_depth H2) ; destruct_exists.
  subst t'.
  inversion H34.
  subst a4 ; subst a5.
  exists a6.
  assert (Heq:=unique_sort (refl_l (fromd H35)) (coerce_refl_r H11)).
  subst c.
  assert (Heq:=unique_sort (refl_l (fromd H37)) (refl_l (fromd H14))).
  subst c1.
  pose (generation_pair H4) ; destruct_exists.
  inversion H51 ; subst.
  inversion H44 ; subst.
  assert (Heq:=unique_sort (refl_r (fromd H35)) (refl_l H46)).
  subst c.
  assert(coerce_in_env (a4 :: G) (a0 :: G)).
  apply coerce_env_hd with s1 ; eauto with coc ecoc.
  assert(a0 :: G |-- a5 -> b13 : c1).
  apply tposr_coerce_env with (a4 :: G) ; eauto with coc ecoc.
  assert (Heq:=unique_sort (refl_l H53) (refl_r (fromd H37))).
  subst c1.

  assert(coerce_in_env (a :: G) (A' :: G)) by eauto with coc ecoc.
  assert(G |-- B0 >-> a : s1).
  destruct H10.
  destruct H10.
  subst a.
  elim (tposr_not_kind (coerce_refl_l H11)).
  destruct H10.
  rewrite (unique_sort (coerce_refl_r H10) (coerce_refl_l H)) in H10.
  assumption.

   assert(G |-- Pi1_l (Sum_l A' B') (Pair_l (Sum_l a4 a5) a8 a9) -> x5 : B0).
  apply tposr_conv with A' s1.
  apply tposr_pi1_red with b12 s1 b13 s2 x4 x6 ; auto with coc.
  apply tposr_equiv_l with (Sum_l a b) ; auto with coc.
  right ; exists x4 ; auto.
  eauto with coc ecoc.
  apply tposr_coerce_trans with a ; auto with coc.
  apply tposr_coerce_trans with a0 ; eauto with coc ecoc.
  apply tposr_coerce_trans with b ; auto with coc.
  apply coerce_coerce_env with (a :: G) ; auto.
  auto with coc ecoc.
  apply tposr_coerce_trans with b0 ; auto with coc ecoc.
  apply coerce_coerce_env with (a :: G) ; auto.
  apply coerce_coerce_env with (a0 :: G) ; eauto with coc ecoc.

  unfold equiv_sort in H52.
  apply tposr_coerce_trans with (Sum_l a b) ; auto.
  apply tposr_coerce_sum with s1 s2 ; auto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply coerce_coerce_env with (a :: G) ; auto with coc ecoc.
  apply tposr_coerce_env with (a :: G) ; eauto with coc ecoc.
  apply tposr_coerce_env with (a :: G) ; eauto with coc ecoc.
  apply tposr_coerce_trans with a ; auto with coc.
  
  assert(G |-- b1 -> x5 : a).
  apply tposr_conv with a2 s1 ; auto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_coerce_trans with a0 ; auto with coc ecoc.
  pose (fromd H6) ; auto with coc ecoc.

  intuition.
  apply tposr_conv with B0 s1 ; auto.
  apply tposr_conv with a s1 ; auto with coc.

  (* Pi1_red *)
  intros.
  subst N.
  subst A''.
  subst e.
  subst M.
  pose (generation_pair_depth H2) ; destruct_exists.
  inversion H5.
  subst A0 a0.
  clear H5.
  inversion H17.
  subst b b0 a1 a2.
  assert(Heq:=unique_sort (fromd H6) (fromd H)).
  subst c.
  assert(Heq:=unique_sort (fromd H8) (fromd H0)).
  subst c0.
  assert(G |-- A >-> A' : s1). 
  pose (fromd H) ; apply tposr_coerce_trans with a ; auto with coc ecoc.
  
  pose (generation_pi1_depth H10) ; destruct_exists.
  inversion H19.
  subst a0 B''.
  assert(Heq:=unique_sort (coerce_refl_l H21) (coerce_refl_l H5)).
  subst c.
  assert(Heq:=unique_sort (coerce_refl_l H4) (coerce_refl_l H22)).
  subst d1.
  
  destruct (H20).
  destruct H20.
  subst A.
  elim (tposr_not_kind (coerce_refl_l H3)).
  destruct H20.
  rewrite (unique_sort (coerce_refl_r H20) (coerce_refl_l H5)) in H20.
  clear x1.
  
  assert(coerce_in_env (a :: G) (A :: G)).
  apply coerce_env_hd with s1 ; auto with coc.
  
  destruct H23 ; destruct_exists.
  
  (* Pi1_red, Pi1 *)
  subst P.
  
  pose (generation_pair_depth H23).
  destruct_exists.
  inversion H25.
  subst a2 a3.
  assert(Heq:=unique_sort (fromd H26) (fromd H)).
  subst c.
  assert(Heq:=unique_sort (fromd H28) (fromd H8)).
  subst c0.
  subst a0.
  assert(b1 < x) by (rewrite <- H9 ; apply lt_trans with p ; auto with arith).
  pose (IH _ H35 _ _ _ _ _ H13 _ _ H31) ; destruct_exists.
  exists x2.

  pose (fromd H26) ; pose (fromd H28) ; pose (fromd H31) ; pose (fromd H33).
  assert(G |-- a1 >-> b4 : s1).
  apply tposr_coerce_trans with A ; eauto with coc.
  apply tposr_coerce_trans with a ; eauto with coc.


  assert(a1 :: G |-- b0 >-> b5 : s2).
  apply coerce_coerce_env with (a :: G) ; auto with coc.
  apply tposr_coerce_trans with B ; auto with coc.
  apply tposr_coerce_trans with b ; auto with coc.
  apply coerce_coerce_env with (A :: G) ; auto with coc.
  apply coerce_coerce_env with (A :: G) ; auto with coc.
  apply coerce_env_hd with s1 ; auto with coc.
  apply tposr_coerce_trans with A ; auto with coc.
  
  assert(G |-- Pi1_l (Sum_l a1 b0) (Pair_l (Sum_l b4 b5) a4 a5) -> x2 : A).
  apply tposr_conv with a1 s1 ; try apply (fromd H5) ; auto with coc.
  assert(coerce_in_env (a :: G) (b4 :: G)).
  apply coerce_env_hd with s1 ; eauto with coc ecoc.

  apply tposr_pi1_red with b4 s1 b5 s2 s3 a5 ; auto with coc.
  eauto with coc.
  apply tposr_coerce_env with (a :: G) ; eauto with coc ecoc.
  apply tposr_pair with s1 s2 s3 ; auto with coc ecoc.
  eauto with coc.
  apply tposr_coerce_env with (a :: G) ; eauto with coc ecoc.
  apply tposr_conv with a s1 ; eauto with coc ecoc.
  apply tposr_conv with (lsubst u B) s2 ; auto with coc.
  eauto with coc.
  apply substitution_tposr_coerce with a ; auto with coc.
  eauto with coc.

  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.

  intuition ; auto with coc.
  apply tposr_conv with a s1 ; auto with coc.
  apply tposr_conv with A s1 ; auto with coc.
  apply tposr_conv with a s1 ; auto with coc.
  apply tposr_conv with A s1 ; auto with coc.

  (* Pi1_red, Pi1_red *)
  inversion H23.
  subst a1 b0 a0 c.
  clear H19 H23 H17.
  subst P.
  pose (generation_pair_depth H29) ; destruct_exists.
  inversion H17.
  subst a0 a1.
  inversion H38.
  subst b0 b6 b3 d1.
  
  assert(b1 < x) by (rewrite <- H9 ; apply lt_trans with p ; auto with arith).
  pose (IH _ H40 _ _ _ _ _ H13 _ _ H34) ; destruct_exists.
  exists x3.

  assert(equiv G B0 a).
  right ; exists s1 ; eauto with coc.
  apply tposr_coerce_trans with A ; auto with coc.

  assert(equiv G A a).
  right ; exists s1 ; eauto with coc.

  intuition ; try apply tposr_equiv_r with a ; auto.

  (* Pi2 *)
  intros.
  pose (generation_pi2_depth H8) ; destruct_exists.
  inversion H9.
  subst A.
  subst A0.
  subst B.
  subst e.

  destruct H13 ; destruct_exists.

  (* Pi2, Pi2 *)
  rewrite H6.
  subst M.
  subst N.

  assert(p < x) by (rewrite <- H7 ; auto with arith).
  pose (IH _ H4 _ _ _ _ _ H2 _ _ H3) ; destruct_exists ; clear H4.

  exists (Pi2_l (Sum_l A' B') x0).

  assert (Heq:=unique_sort (coerce_refl_l H11) (coerce_refl_l H)).
  subst c.
  assert (Heq:=unique_sort (coerce_refl_l H12) (coerce_refl_l H0)).
  subst d.

  assert(G |-- a0 >-> A' : s1).
  apply tposr_coerce_trans with a ; eauto with coc.

  assert(coerce_in_env (a :: G) (A' :: G)).
  apply coerce_env_hd with s1 ; eauto with coc.

  assert(G |-- Pi2_l (Sum_l A' B') t' -> Pi2_l (Sum_l A' B') x0 : lsubst (Pi1_l (Sum_l a b) t) b).
  apply tposr_conv with (lsubst (Pi1_l (Sum_l A' B') t') B') s2 ; auto with coc.
  apply tposr_pi2 with s1 s2 s3 ;  auto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply coerce_coerce_env with (a :: G) ; eauto with coc ecoc.
  apply tposr_conv with (Sum_l a b) s3 ; auto with coc.
  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.

  assert(coerce_in_env (a :: G) (a0 :: G)).
  apply coerce_env_hd with s1 ; eauto with coc.

  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with a ; auto with coc.
  apply tposr_pi1 with s1 s2 s3 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.


  assert(G |-- Pi2_l (Sum_l a0 b0) a1 -> Pi2_l (Sum_l A' B') x0 : lsubst (Pi1_l (Sum_l a b) t) b).
  apply tposr_conv with (lsubst (Pi1_l (Sum_l a0 b0) a1) b0) s2 ; auto with coc.
  apply tposr_pi2 with s1 s2 s3 ;  auto with coc ecoc.
  eauto with coc ecoc.
  apply coerce_coerce_env with (a :: G) ; eauto with coc ecoc.
  apply tposr_conv with (Sum_l a b) s3 ; auto with coc.
  assert(coerce_in_env (a :: G) (a0 :: G)).
  apply coerce_env_hd with s1 ; eauto with coc.

  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.

  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with a ; auto with coc.
  apply tposr_pi1 with s1 s2 s3 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.

  intuition ; try apply tposr_equiv_r with (lsubst (Pi1_l (Sum_l a b) t) b) ; auto with coc ecoc.
  
  (* Pi2, Pi2_red *)
  subst P.
  subst t.
  subst N.
  subst M.
  assert (Heq:=unique_sort (coerce_refl_l H11) (coerce_refl_l H)).
  subst c.
  assert (Heq:=unique_sort (coerce_refl_l H12) (coerce_refl_l H0)).
  subst d.
 
  assert(p < x) by  (rewrite <- H7 ; auto with arith).  
  pose (IH _ H3 _ _ _ _ _ H2 _ _ H16) ; destruct_exists.
  pose (tod H18).
  destruct_exists.
  pose (generation_pair_depth H20) ; destruct_exists.
  inversion H21.
  subst a4 ; subst a5.
  subst x1.
  assert (Heq:=unique_sort (refl_l (fromd H22)) (refl_r (fromd H6))).
  subst c.
  assert(coerce_in_env (a2 :: G) (a0 :: G)).
  apply coerce_env_hd with s1 ; eauto with coc ecoc.
  assert(a0 :: G |-- a3 -> b5 : c1).
  apply tposr_coerce_env with (a2 :: G) ; eauto with coc ecoc.
  assert (Heq:=unique_sort (refl_r (fromd H14)) (refl_l H33)).
  subst c1.

  pose (generation_pair_depth H2) ; destruct_exists.
  subst t'.
  inversion H34.
  subst a4 ; subst a5.

  exists a7.

  assert (Heq:=unique_sort (refl_l (fromd H35)) (coerce_refl_r H11)).
  subst c.
  assert (Heq:=unique_sort (refl_l (fromd H37)) (refl_l (fromd H14))).
  subst c1.
  pose (generation_pair H4) ; destruct_exists.
  inversion H51 ; subst.
  inversion H44 ; subst.
  assert (Heq:=unique_sort (refl_r (fromd H35)) (refl_l H46)).
  subst c.
  assert(coerce_in_env (a4 :: G) (a0 :: G)).
  apply coerce_env_hd with s1 ; eauto with coc ecoc.
  assert(a0 :: G |-- a5 -> b13 : c1).
  apply tposr_coerce_env with (a4 :: G) ; eauto with coc ecoc.
  assert (Heq:=unique_sort (refl_l H53) (refl_r (fromd H37))).
  subst c1.

  assert(coerce_in_env (a :: G) (A' :: G)) by eauto with coc ecoc.
  assert(Htpi1:G |-- lsubst (Pi1_l (Sum_l a b) (Pair_l (Sum_l a0 b0) a1 c0)) b -> lsubst (Pi1_l (Sum_l a b) (Pair_l (Sum_l a0 b0) a1 c0)) b: s2).
  apply substitution_sorted with a ; auto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_pi1 with s1 s2 s3 ; eauto with coc ecoc.
  
  assert(G |-- B0 >-> lsubst (Pi1_l (Sum_l a b) (Pair_l (Sum_l a0 b0) a1 c0)) b : s2).
  destruct H10.
  destruct H10.
  destruct b ; simpl in H55 ; try discriminate.
  unfold lsubst in H55 ; simpl in H55.
  rewrite H55 in H0.
  elim (tposr_not_kind (coerce_refl_l H0)).
  unfold lsubst in H55.
  destruct (inv_subst_sort _ _ _ H55) ; try discriminate.
  destruct H10.
  rewrite (unique_sort (coerce_refl_r H10) Htpi1) in H10.
  assumption.

   assert(G |-- Pi2_l (Sum_l A' B') (Pair_l (Sum_l a4 a5) a8 a9) -> x6 :  lsubst (Pi1_l (Sum_l a b) (Pair_l (Sum_l a0 b0) a1 c0)) b).
  apply tposr_conv with (lsubst (Pi1_l (Sum_l A' B')  (Pair_l (Sum_l a4 a5) a8 a9)) B') s2.
  apply tposr_pi2_red with b12 s1 b13 s2 x4 x5 ; auto with coc.
  apply tposr_equiv_l with (Sum_l a b) ; auto with coc.
  right ; exists x4 ; auto.
  eauto with coc ecoc.
  apply tposr_coerce_trans with a ; auto with coc.
  apply tposr_coerce_trans with a0 ; eauto with coc ecoc.
  apply tposr_coerce_trans with b ; auto with coc.
  apply coerce_coerce_env with (a :: G) ; auto.
  auto with coc ecoc.
  apply tposr_coerce_trans with b0 ; auto with coc ecoc.
  apply coerce_coerce_env with (a :: G) ; auto.
  apply coerce_coerce_env with (a0 :: G) ; eauto with coc ecoc.

  unfold equiv_sort in H52.
  apply tposr_coerce_trans with (Sum_l a b) ; auto.
  apply tposr_coerce_sum with s1 s2 ; auto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply coerce_coerce_env with (a :: G) ; auto with coc ecoc.
  apply tposr_coerce_env with (a :: G) ; eauto with coc ecoc.
  apply tposr_coerce_env with (a :: G) ; eauto with coc ecoc.
  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with a ; auto with coc.
  apply tposr_pi1 with s1 s2 s3 ; eauto with coc ecoc.
  
  assert(G |-- d0 -> x6 : B0).
  apply tposr_conv with (lsubst b1 a3) s2 ; auto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_coerce_trans with (lsubst (Pi1_l (Sum_l a b) (Pair_l (Sum_l a0 b0) a1 c0)) b) ; auto with coc ecoc.
  apply tposr_coerce_sym.
  apply tposr_coerce_trans with (lsubst a8 b).
  apply substitution_tposr_coerce with a ; auto with coc.
  apply tposr_coerce_trans with b0 ; auto with coc ecoc.
  apply tposr_pi1_red with a0 s1 b0 s2 s3 a9 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_pair with s1 s2 s3 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.
  apply tposr_coerce_trans with (lsubst x5 b).
  apply substitution_tposr_coerce with a ; eauto with coc ecoc.
  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with a0. 
  apply tposr_coerce_trans with b0.
  eauto with coc ecoc.
  apply coerce_coerce_env with (a :: G).
  auto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.

  intuition.
  apply tposr_conv with (  lsubst (Pi1_l (Sum_l a b) (Pair_l (Sum_l a0 b0) a1 c0)) b) s2 ; auto with coc.
  apply tposr_conv with B0 s2 ; auto with coc.

  (* Pi2_red *)
  intros.
  subst e.
  subst N.
  subst M.
  pose (generation_pair_depth H2) ; destruct_exists.
  inversion H5.
  subst A0 a0.
  clear H5.
  inversion H18.
  subst b b0 a1 a2.
  assert(Heq:=unique_sort (fromd H6) (fromd H)).
  subst c.
  assert(Heq:=unique_sort (fromd H11) (fromd H0)).
  subst c0.

  assert(G |-- A'' >-> A' : s1). 
  pose (fromd H) ; apply tposr_coerce_trans with a ; auto with coc ecoc.
  
  pose (generation_pi2_depth H10) ; destruct_exists.
  inversion H20.
  subst a0 B''.
  assert(Heq:=unique_sort (coerce_refl_l H22) (coerce_refl_l H5)).
  subst c.
  assert(Heq:=unique_sort (coerce_refl_l H4) (coerce_refl_l H23)).
  subst d1.

  assert(coerce_in_env (A'' ::G) (a :: G)).
  eauto with coc ecoc.

  assert(G |-- lsubst (Pi1_l (Sum_l A'' b) (Pair_l (Sum_l a B) u v)) b ->
  lsubst (Pi1_l (Sum_l A'' b) (Pair_l (Sum_l a B) u v)) b : s2).
  apply substitution_sorted with A'' ; auto with coc.
  eauto with coc.
  apply tposr_pi1 with s1 s2 s3 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_conv with (Sum_l a B) s3 ; auto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_coerce_sum with s1 s2 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply coerce_coerce_env with (A'' :: G) ; auto.
  auto with coc ecoc.
  apply tposr_coerce_env with (A'' :: G) ; eauto with coc ecoc.
  apply tposr_coerce_env with (A'' :: G) ; eauto with coc ecoc.

  destruct H21.
  destruct H21.
  destruct (inv_subst_sort _ _ _ H27) ; try discriminate.
  subst b.
  elim (tposr_not_kind (coerce_refl_l H4)).
  destruct H21.
  rewrite (unique_sort (coerce_refl_r H21) (refl_l H26)) in H21.
  clear x1.
  
  destruct H24 ; destruct_exists.
  
  (* Pi1_red, Pi1 *)
  subst P.
  
  pose (generation_pair_depth H24).
  destruct_exists.
  inversion H27.
  subst a2 a3.
  assert(Heq:=unique_sort (fromd H28) (fromd H)).
  subst c.
  assert(Heq:=unique_sort (fromd H30) (fromd H11)).
  subst c0.
  subst a0.
  assert(b2 < x) by (rewrite <- H9 ; apply lt_trans with p ; auto with arith).
  pose (IH _ H37 _ _ _ _ _ H16 _ _ H35) ; destruct_exists.
  exists x2.

  pose (fromd H28) ; pose (fromd H30) ; pose (fromd H33) ; pose (fromd H35).
  assert(G |-- a1 >-> b4 : s1).
  apply tposr_coerce_trans with A'' ; eauto with coc.
  apply tposr_coerce_trans with a ; eauto with coc.

  assert(a1 :: G |-- b0 >-> b5 : s2).
  apply coerce_coerce_env with (a :: G) ; auto with coc.
  apply tposr_coerce_trans with B ; auto with coc.
  apply tposr_coerce_trans with b ; auto with coc.
  apply coerce_coerce_env with (A'' :: G) ; auto with coc.
  apply coerce_coerce_env with (A'' :: G) ; auto with coc.
  apply coerce_env_hd with s1 ; auto with coc.
  apply tposr_coerce_trans with A'' ; auto with coc.
  
  assert(coerce_in_env (a :: G) (b4 :: G)).
  apply coerce_env_hd with s1 ; eauto with coc ecoc.

  assert(G |-- Pi2_l (Sum_l a1 b0) (Pair_l (Sum_l b4 b5) a4 a5) -> x2 : lsubst (Pi1_l (Sum_l A'' b) (Pair_l (Sum_l a B) u v)) b).
  apply tposr_conv with (lsubst (Pi1_l (Sum_l a1 b0) (Pair_l (Sum_l b4 b5) a4 a5)) b0) s2 ; try apply (fromd H5) ; auto with coc.
  apply tposr_pi2_red with b4 s1 b5 s2 s3 a4 ; auto with coc.
  eauto with coc.
  apply tposr_coerce_env with (a :: G) ; eauto with coc ecoc.
  apply tposr_pair with s1 s2 s3 ; auto with coc ecoc.
  eauto with coc.
  apply tposr_coerce_env with (a :: G) ; eauto with coc ecoc.
  apply tposr_conv with a s1 ; eauto with coc ecoc.
  apply tposr_conv with (lsubst u B) s2 ; auto with coc.
  apply substitution_tposr_coerce with a ; auto with coc.
  eauto with coc.

  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.

  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with A'' ; auto with coc.
  apply tposr_pi1 with s1 s2 s3 ; auto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.

  assert(G |-- v' -> x2 : lsubst (Pi1_l (Sum_l A'' b) (Pair_l (Sum_l a B) u v)) b).
  apply tposr_conv with (lsubst u B) s2 ; auto with coc.
  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with A'' ; auto with coc.
  apply tposr_pi1_red with a s1 B s2 s3 v; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_pair with s1 s2 s3 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.

  intuition ; auto with coc.
  apply tposr_conv with (lsubst (Pi1_l (Sum_l A'' b) (Pair_l (Sum_l a B) u v)) b) s2 ; auto with coc ecoc.
  apply tposr_conv with (lsubst (Pi1_l (Sum_l A'' b) (Pair_l (Sum_l a B) u v)) b) s2 ; auto with coc ecoc.

  (* Pi2_red, Pi2_red *)
  inversion H24.
  subst a1 b0 a0 c.
  subst P.
  pose (generation_pair_depth H31) ; destruct_exists.
  inversion H33.
  subst a0 a1.
  inversion H43.
  subst b0 b6 b3 d1.
  
  assert(b2 < x) by (rewrite <- H9 ; apply lt_trans with p ; auto with arith).
  pose (IH _ H45 _ _ _ _ _ H16 _ _ H41) ; destruct_exists.
  exists x3.

  assert(G |-- lsubst (Pi1_l (Sum_l A'' b) (Pair_l (Sum_l a B) u v)) b >-> lsubst u B : s2).
  apply substitution_tposr_coerce with A'' ; auto with coc.
  apply tposr_pi1_red with a s1 B s2 s3 v; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_pair with s1 s2 s3 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_coerce_sum with s1 s2 ; eauto with coc ecoc.
  
  assert(G |-- B0 >-> lsubst u B : s2).
  apply tposr_coerce_trans with (lsubst (Pi1_l (Sum_l A'' b) (Pair_l (Sum_l a B) u v)) b) ; auto.

  intuition ;
  apply tposr_conv with (lsubst u B) s2 ; auto with coc.
Qed.