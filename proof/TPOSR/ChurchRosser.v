Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.MyList.

Require Import TPOSR.Terms.
Require Import TPOSR.Reduction.
Require Import TPOSR.Conv.
Require Import TPOSR.LiftSubst.
Require Import TPOSR.Env.
Require Import TPOSR.Types.
Require Import TPOSR.Basic.
Require Import TPOSR.Thinning.
Require Import TPOSR.LeftReflexivity.
Require Import TPOSR.Substitution.
Require Import TPOSR.CtxConversion.
Require Import TPOSR.RightReflexivity.
Require Import TPOSR.Generation.
Require Import TPOSR.TypesDepth.
Require Import TPOSR.TypesFunctionality.
Require Import TPOSR.UniquenessOfTypes.
(*Require Import TPOSR.CtxConversionDepth.*)


Require Import Meta.TPOSR_Russell.

Require Import TPOSR.MaxLemmas.

Set Implicit Arguments.

Definition tod := tposr_tposrd_type.
Definition fromd := tposrd_tposr_type.

Lemma tposr_equiv_l : forall e A B, equiv e A B -> forall M N, 
  e |-- M -> N : A -> e |-- M -> N : B.
Proof.
  destruct 1 ; intros.
  rewrite <- H ; assumption.
  destruct H.
  apply tposr_conv_l with A x ; auto.
Qed. 

Lemma tposr_equiv_r : forall e A B, equiv e A B -> forall M N, 
  e |-- M -> N : B -> e |-- M -> N : A.
Proof.
  destruct 1 ; intros.
  rewrite H ; assumption.
  destruct H.
  apply tposr_conv_r with B x ; auto.
Qed. 

Theorem church_rosser : forall n m,
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
  pose (generation_prod Hr) ; destruct_exists.
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
  pose (generation_lambda Hr) ; destruct_exists.
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
  exists (Abs_l x0 x1) ; intuition ; try apply tposr_abs with s1 ; 
  try apply tposr_abs with b ; auto with coc.

  apply tposr_exp with (Prod_l A' B) s2 ; auto with coc.
  apply tposr_abs with s1 B' s2 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply (fromd H0).
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_prod with s1 ; auto with coc.
  apply (fromd H).
  apply (left_refl (fromd H0)).

  apply tposr_equiv_r with (Prod_l A0 a1) ; auto.
  apply tposr_exp with (Prod_l A' a1) b0 ; auto with coc.
  apply tposr_abs with b b1 b0 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply (fromd H11).
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_prod with s1 ; auto with coc.
  apply (fromd H).
  apply (left_refl (fromd H11)).

  apply tposr_exp with (Prod_l a B) s2 ; auto with coc.
  apply tposr_abs with s1 B' s2 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply (fromd H0).
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_prod with b ; auto with coc.
  apply (fromd H7).
  apply (left_refl (fromd H0)).

  apply tposr_equiv_r with (Prod_l A0 a1) ; auto.
  apply tposr_exp with (Prod_l a a1) b0 ; auto with coc.
  apply tposr_abs with b b1 b0 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply (fromd H11).
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_prod with b ; auto with coc.
  apply (fromd H7).
  apply (left_refl (fromd H11)).

  (* App *)
  intros P B0 Hr.
  pose (generation_app Hr) ; destruct_exists.

  assert(q < x) ; try rewrite <- H7 ; auto with arith.
  pose (IH _ H16 _ _ _ _ _ H2 _ _ H12) ; destruct_exists.
  pose (uniqueness_of_types (toq H2) (toq H12)).
  assert(c = s1).
  destruct e0 ; destruct_exists.
  rewrite <- H21 in H8.
  apply (tposrd_unique_sort H8 H).
  destruct (conv_refls H21).
  rewrite <- (tposr_unique_sort H22 (fromd H)).
  rewrite <- (tposr_unique_sort H23 (fromd H8)).
  reflexivity.

  assert(A0 :: G |-- B -> a0 : Srt_l b0).
  apply conv_env with (a :: G) ; auto with coc.
  apply (fromd H10).
  destruct e0.
  rewrite H22.
  apply conv_env_hd with c.
  apply tposr_eq_tposr.
  apply (left_refl (fromd H8)).
  destruct H22.
  apply conv_env_hd with x1 ; auto with coc.

  assert(a :: G |-- B -> B' : Srt_l s2).
  apply conv_env with (A0 :: G) ; auto with coc.
  apply (fromd H0).
  destruct e0.
  rewrite H23.
  apply conv_env_hd with c.
  apply tposr_eq_tposr.
  apply (left_refl (fromd H8)).
  destruct H23.
  apply conv_env_hd with x1 ; auto with coc.

  assert(b0 = s2).
  pose (left_refl H22).
  pose (left_refl (fromd H0)).
  apply (tposr_unique_sort t t0).
  rewrite H21 in H8.
  rewrite H24 in H10.
  rewrite H24 in H22.
  rewrite H24 in H14.

  assert(m0 < x) by rewrite <- H7 ; auto with arith. 
  pose (tod H22) ; destruct_exists.
  pose (IH _ H25 _ _ _ _ _ H0 _ _ H26) ; destruct_exists.

  assert(G |-- lsubst x0 x2 ~= lsubst N0 B : s2).
  apply tposr_eq_sym.
  apply tposr_eq_trans with (lsubst a1 a0).
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst N0 (Srt_l s2)).
  apply substitution with A0 ; auto with coc.
  pose (right_refl (fromd H12)).
  pose (left_refl H19).
  pose (tposr_uniqueness_of_types t t0).
  apply tposr_equiv_l with a ; auto with coc.
  apply (fromd H12).

  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst a1 (Srt_l s2)).
  apply substitution with A0 ; auto with coc.

  assert(HeqB: equiv G B0 (lsubst N0 B)).
  right ; exists s2 ; assumption.

  destruct H15 ; destruct_exists.

  (* App, App *)
  rewrite H33.
  assert(p < x) ; try rewrite <- H7 ; auto with arith.
  pose (IH _ H34 _ _ _ _ _ H1 _ _ H15) ; destruct_exists.
  
  assert(G |-- App_l B' M' N' -> App_l x2 x3 x0 : lsubst N0 B).

  apply tposr_conv_l with (lsubst N' B') s2 ; auto with coc.
  apply tposr_eq_trans with (lsubst x0 x2) ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst N' (Srt_l s2)).
  apply substitution with A0 ; auto with coc.

  apply tposr_app with A0 A' s1 s2 ; auto with coc.
  apply (fromd H).
  apply tposr_conv_l with (Prod_l A0 B) s2 ; auto with coc.
  apply tposr_eq_tposr.
  apply tposr_prod with s1 ; auto with coc.
  apply (left_refl (fromd H)).
  apply (fromd H0).

  assert(G |-- App_l a0 a2 a1 -> App_l x2 x3 x0 : lsubst N0 B).

  apply tposr_conv_l with (lsubst a1 a0) s2 ; auto with coc.
  apply tposr_eq_trans with (lsubst x0 x2) ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst a1 (Srt_l s2)).
  apply substitution with A0 ; auto with coc.

  apply tposr_app with A0 A' s1 s2 ; auto with coc.
  apply (fromd H).
  apply tposr_conv_l with (Prod_l A0 B) s2 ; auto with coc.
  apply tposr_eq_tposr.
  apply tposr_prod with s1 ; auto with coc.
  apply (left_refl (fromd H)).

  exists (App_l x2 x3 x0) ; intuition ; auto with coc.
  apply tposr_equiv_r with (lsubst N0 B) ; auto with coc.
  apply tposr_equiv_r with (lsubst N0 B) ; auto with coc.

  (* App, Beta *)
  rewrite H34.
  rewrite H15 in H1.
  pose (generation_lambda H1) ; destruct_exists.
  assert(c3 < x).
  rewrite <- H7 ; auto with arith.
  apply lt_trans with p ; auto with arith.
  pose (IH _ H43 _ _ _ _ _ H37 _ _ H32) ; destruct_exists.
  assert(c2 < x).
  rewrite <- H7 ; auto with arith.
  apply lt_trans with p ; auto with arith.
  pose (IH _ H48 _ _ _ _ _ H35 _ _ H8) ; destruct_exists.

  assert(G |-- a ~= a3 : b3).
  apply tposr_eq_tposr ; auto with coc.
  apply (fromd H35).
  assert (conv_in_env (a :: G) (a3 :: G)).
  apply conv_env_hd with b3 ; auto.

  assert (conv_in_env (A0 :: G) (a3 :: G)).
  destruct e0.
  rewrite H55.
  apply H54.
  destruct H55.
  apply conv_env_hd with x5.
  apply tposr_eq_trans with a ; auto with coc.
  apply tposr_eq_tposr.
  destruct (conv_refls H55).
  pose (tposr_unique_sort H57 (fromd H35)).
  rewrite e0 ; auto.
  apply (fromd H35).

  exists (lsubst x0 x3).

  assert(G |-- App_l B' M' N' -> lsubst x0 x3 : lsubst N0 B).

  apply tposr_conv_l with (lsubst N' B') s2 ; auto with coc.
  apply tposr_eq_trans with (lsubst x0 x2) ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst N' (Srt_l s2)).
  apply substitution with A0 ; auto with coc.
  
  rewrite H41.
  apply tposr_beta with x4 s1 x2 s2 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply conv_env with (a :: G) ; auto with coc.
  apply tposr_red with B s2 ; auto with coc.
  apply tposr_conv_l with a b3 ; auto with coc.

  assert(G |-- lsubst a1 b2 -> lsubst x0 x3 : lsubst N0 B).

  apply tposr_conv_l with (lsubst a1 B') s2 ; auto with coc.
  apply tposr_eq_trans with (lsubst x0 x2) ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst a1 (Srt_l s2)).
  apply substitution with A0 ; auto with coc.
  apply substitution with a ; auto with coc.
  apply tposr_red with B s2 ; auto with coc.

  intuition ; auto with coc.

  apply tposr_equiv_r with (lsubst N0 B) ; auto.
  apply tposr_equiv_r with (lsubst N0 B) ; auto.

  (* Beta *)
  intros P B0 Hr.
  pose (generation_app Hr) ; destruct_exists.

  assert(q < x) ; try rewrite <- H7 ; auto with arith.
  pose (IH _ H16 _ _ _ _ _ H2 _ _ H12) ; destruct_exists.
  pose (uniqueness_of_types (toq H2) (toq H12)).
  assert(c = s1).
  destruct e0 ; destruct_exists.
  rewrite <- H21 in H8.
  apply (tposrd_unique_sort H8 H).
  destruct (conv_refls H21).
  rewrite <- (tposr_unique_sort H22 (fromd H)).
  rewrite <- (tposr_unique_sort H23 (fromd H8)).
  reflexivity.

  assert(A0 :: G |-- B -> a0 : Srt_l b0).
  apply conv_env with (a :: G) ; auto with coc.
  apply (fromd H10).
  destruct e0.
  rewrite H22.
  apply conv_env_hd with c.
  apply tposr_eq_tposr.
  apply (left_refl (fromd H8)).
  destruct H22.
  apply conv_env_hd with x1 ; auto with coc.

  assert(a :: G |-- B -> B' : Srt_l s2).
  apply conv_env with (A0 :: G) ; auto with coc.
  apply (fromd H0).
  destruct e0.
  rewrite H23.
  apply conv_env_hd with c.
  apply tposr_eq_tposr.
  apply (left_refl (fromd H8)).
  destruct H23.
  apply conv_env_hd with x1 ; auto with coc.

  assert(b0 = s2).
  pose (left_refl H22).
  pose (left_refl (fromd H0)).
  apply (tposr_unique_sort t t0).
  rewrite H21 in H8.
  rewrite H24 in H10.
  rewrite H24 in H22.
  rewrite H24 in H14.

  assert(m0 < x) by rewrite <- H7 ; auto with arith. 
  pose (tod H22) ; destruct_exists.
  pose (IH _ H25 _ _ _ _ _ H0 _ _ H26) ; destruct_exists.

  assert(G |-- lsubst x0 x2 ~= lsubst N0 B : s2).
  apply tposr_eq_sym.
  apply tposr_eq_trans with (lsubst a1 a0).
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst N0 (Srt_l s2)).
  apply substitution with A0 ; auto with coc.
  pose (right_refl (fromd H12)).
  pose (left_refl H19).
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
  pose (generation_lambda H15) ; destruct_exists.
  assert(p < x).
  rewrite <- H7 ; auto with arith.
  pose (IH _ H42 _ _ _ _ _ H1 _ _ H36) ; destruct_exists.
  assert(n0 < x).
  rewrite <- H7 ; auto with arith.
  pose (IH _ H47 _ _ _ _ _ H _ _ H34) ; destruct_exists.

  assert(G |-- A0 ~= a3 : b3).
  apply tposr_eq_tposr ; auto with coc.
  apply (fromd H34).
  assert (conv_in_env (A0 :: G) (a3 :: G)).
  apply conv_env_hd with b3 ; auto.

  assert (conv_in_env (a :: G) (a3 :: G)).
  destruct e0.
  rewrite <- H54.
  apply H53.
  destruct H54.
  apply conv_env_hd with x5.
  apply tposr_eq_trans with A0 ; auto with coc.
  apply tposr_eq_tposr.
  destruct (conv_refls H54).
  pose (tposr_unique_sort H55 (fromd H34)).
  rewrite e0 ; auto.
  apply (fromd H34).

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
  apply tposr_red with B s2 ; auto with coc.
  apply tposr_conv_l with A0 b3 ; auto with coc.

  assert(G |-- lsubst N' M' -> lsubst x0 x3 : lsubst N0 B).

  apply tposr_conv_l with (lsubst N' a0) s2 ; auto with coc.
  apply tposr_eq_trans with (lsubst x0 x2) ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst N' (Srt_l s2)).
  apply substitution with A0 ; auto with coc.
  apply substitution with A0 ; auto with coc.
  apply tposr_red with B s2 ; auto with coc.

  intuition ; auto with coc.

  apply tposr_equiv_r with (lsubst N0 B) ; auto.
  apply tposr_equiv_r with (lsubst N0 B) ; auto.

  (* Beta, Beta *)
  rewrite H34.
  assert(p < x) ; try rewrite <- H7 ; auto with arith.
  inversion H15.
  rewrite <- H38 in H32.

  assert(conv_in_env (a :: G) (A0 :: G)).
  destruct e0.
  rewrite H36.
  apply conv_env_hd with s1.
  apply tposr_eq_tposr.
  apply (left_refl (fromd H8)).
  destruct H36.
  apply conv_env_hd with x3 ; auto with coc.

  assert(A0 :: G |-- M0 -> b2 : B).
  apply conv_env with (a :: G) ; auto with coc core.
  apply (fromd H32).
  
  pose (tod H39) ; destruct_exists.
  pose (IH _ H35 _ _ _ _ _ H1 _ _ H40) ; destruct_exists.
  
  exists (lsubst x0 x4).

  assert(G |-- lsubst N' M' -> lsubst x0 x4 : lsubst N0 B).
  apply tposr_conv_l with (lsubst N' B') s2 ; auto with coc.
  apply tposr_eq_trans with (lsubst x0 x2) ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst N' (Srt_l s2)).
  apply substitution with A0 ; auto with coc.
  apply substitution with A0 ; auto with coc.
  apply tposr_red with B s2 ; auto with coc.
  apply conv_env with (a :: G) ; auto with coc.

  assert(G |-- lsubst a1 b2 -> lsubst x0 x4 : lsubst N0 B).
  apply tposr_conv_l with (lsubst a1 B') s2 ; auto with coc.
  apply tposr_eq_trans with (lsubst x0 x2) ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst a1 (Srt_l s2)).
  apply substitution with A0 ; auto with coc.
  apply substitution with A0 ; auto with coc.
  apply tposr_red with B s2 ; auto with coc.
  apply conv_env with (a :: G) ; auto with coc.

  intuition.

  apply tposr_equiv_r with (lsubst N0 B) ; auto with coc.
  apply tposr_equiv_r with (lsubst N0 B) ; auto with coc.

  (* Red *)
  intros.
  assert(n0 < x) by rewrite <- H5 ; auto with arith.
  pose (IH _ H7 _ _ _ _ _ H _ _ H6) ; destruct_exists.
  exists x0 ; intuition.
  apply tposr_red with A0 s ; auto with coc.
  apply (fromd H0).
  apply tposr_red with A0 s ; auto with coc.
  apply (fromd H0).

  (* Exp *)
  intros.
  assert(n0 < x) by rewrite <- H5 ; auto with arith.
  pose (IH _ H7 _ _ _ _ _ H _ _ H6) ; destruct_exists.
  exists x0 ; intuition.
  apply tposr_exp with B s ; auto with coc.
  apply (fromd H0).
  apply tposr_exp with B s ; auto with coc.
  apply (fromd H0).
  
  (* Subset *)
  intros.
  pose (generation_subset H6) ; destruct_exists.
  rewrite H11.

  assert(n0 < x) by rewrite <- H5 ; auto with arith.
  assert(m0 < x) by rewrite <- H5 ; auto with arith.
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
  
  intuition ; try apply tposr_equiv_r with (Srt_l set) ; auto with coc.

  (* Sum *)
  rewrite <- H2 in Hl2.
  rewrite <- H3 in Hl2.
  rewrite <- H4 in Hl2.
  intros P B0 Hr.
  pose (generation_sum Hr) ; destruct_exists.
  rewrite H12.

  assert(n0 < x) by rewrite <- H6 ; auto with arith.
  pose (IH _ H14 _ _ _ _ _ H _ _ H7) ; destruct_exists.
  assert(m0 < x) by rewrite <- H6 ; auto with arith.
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
  pose (generation_pair Hr) ; destruct_exists.
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

  assert(n0 < x) by rewrite <- H8 ; auto with arith.
  pose (IH _ H9 _ _ _ _ _ H _ _ H10) ; destruct_exists ; clear H9.
  assert(m0 < x) by rewrite <- H8 ; auto with arith.
  pose (IH _ H9 _ _ _ _ _ H0 _ _ H12) ; destruct_exists ; clear H9.
  assert(p < x) by rewrite <- H8 ; auto with arith.
  pose (IH _ H9 _ _ _ _ _ H2 _ _ H15) ; destruct_exists ; clear H9.
  assert(q < x) by rewrite <- H8 ; auto with arith.
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
  apply tposr_red with A0 s1 ; auto with coc.
  apply tposr_conv_l with (lsubst u B) s2 ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l s2) with (lsubst u (Srt_l s2)).
  apply substitution with A0 ; auto with coc.

  assert(G |-- Pair_l (Sum_l b b0) a1 a2 -> Pair_l (Sum_l x1 x2) x3 x4 : Sum_l A0 B).
  apply tposr_conv_r with (Sum_l b b0) x0 ; auto with coc ; try apply tposr_pair with c c0 x0 ; auto with coc.
  apply tposr_eq_tposr.
  apply tposr_sum with c c0 ; auto with coc.
  apply conv_env with (A0 :: G) ; auto with coc.
  apply tposr_red with A0 c ; auto with coc.
  apply tposr_conv_l with (lsubst u B) c0 ; auto with coc.
  apply tposr_eq_tposr.
  change (Srt_l c0) with (lsubst u (Srt_l c0)).
  apply substitution with A0 ; auto with coc.
   
  intuition ; try apply tposr_equiv_r with (Sum_l A0 B) ; auto.

  (* Pi1 *)
  intros.
  pose (generation_pi1 H8) ; destruct_exists.
  inversion H13.
  rewrite <- H18 in H9.
  rewrite <- H18 in H11.
  rewrite <- H18 in H16.
  rewrite <- H18 in H15.
  rewrite <- H18.
  rewrite <- H19 in H11.
  rewrite <- H19 in H16.

  clear a a0 H19 H18 H13.
  
  assert(n0 < x) by rewrite <- H7 ; auto with arith.
  pose (IH _ H13 _ _ _ _ _ H _ _ H9) ; destruct_exists ; clear H13.
  assert(m0 < x) by rewrite <- H7 ; auto with arith.
  pose (IH _ H13 _ _ _ _ _ H0 _ _ H11) ; destruct_exists ; clear H13.
  assert(p < x) by rewrite <- H7 ; auto with arith.


  assert(conv_in_env (A :: G) (A' :: G)).
  apply conv_env_hd with s1 ; auto with coc.
  apply tposr_eq_tposr ; apply (fromd H).
  assert(conv_in_env (A :: G) (b :: G)).
  apply conv_env_hd with c ; auto with coc.
  apply tposr_eq_tposr ; apply (fromd H9).
  pose (fromd H).
  pose (fromd H0).
  pose (fromd H2).
  pose (fromd H9).
  pose (fromd H11).

  destruct H16 ; destruct_exists.

  (* Pi1, Pi1 *)
  rewrite H29.
  pose (IH _ H13 _ _ _ _ _ H2 _ _ H27) ; destruct_exists ; clear H13.

  exists (Pi1_l (Sum_l x1 x2) x3).
  assert(G |-- Pi1_l (Sum_l A' B') t' -> Pi1_l (Sum_l x1 x2) x3 : A).
  apply tposr_conv_r with A' s1 ; auto with coc ; try apply tposr_pi1 with s1 s2 s3 ; auto with coc.
  apply conv_env with (A :: G) ; auto with coc.
  apply tposr_red with (Sum_l A B) s3 ; auto with coc.
  apply tposr_sum with s1 s2 ; auto with coc.
  
  rewrite H16.
  assert(G |-- Pi1_l (Sum_l b b0) b1 -> Pi1_l (Sum_l x1 x2) x3 : A).
  apply tposr_conv_r with b c ; auto with coc ; try apply tposr_pi1 with c c0 x0 ; auto with coc.
  apply conv_env with (A :: G) ; auto with coc.
  apply tposr_red with (Sum_l A B) x0 ; auto with coc.
  apply tposr_sum with c c0 ; auto with coc.
   
  intuition ; try apply tposr_equiv_r with A ; auto.
  
  (* Pi1, Pi1_red *)
  rewrite H29.
  pose (IH _ H13 _ _ _ _ _ H2 _ _ H27) ; destruct_exists ; clear H13.

  exists (Pi1_l (Sum_l x1 x2) x3).
  assert(G |-- Pi1_l (Sum_l A' B') t' -> Pi1_l (Sum_l x1 x2) x3 : A).
  apply tposr_conv_r with A' s1 ; auto with coc ; try apply tposr_pi1 with s1 s2 s3 ; auto with coc.
  apply conv_env with (A :: G) ; auto with coc.
  apply tposr_red with (Sum_l A B) s3 ; auto with coc.
  apply tposr_sum with s1 s2 ; auto with coc.
  
  rewrite H16.
  assert(G |-- Pi1_l (Sum_l b b0) b1 -> Pi1_l (Sum_l x1 x2) x3 : A).
  apply tposr_conv_r with b c ; auto with coc ; try apply tposr_pi1 with c c0 x0 ; auto with coc.
  apply conv_env with (A :: G) ; auto with coc.
  apply tposr_red with (Sum_l A B) x0 ; auto with coc.
  apply tposr_sum with c c0 ; auto with coc.
   
  intuition ; try apply tposr_equiv_r with A ; auto.




