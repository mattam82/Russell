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
Require Import Lambda.TPOSR.CtxCoercion.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.Equiv.
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.Validity.
Require Import Lambda.TPOSR.TypesDepth.
Require Import Lambda.TPOSR.TypesFunctionality.
Require Import Lambda.TPOSR.UniquenessOfTypes.
Require Import Lambda.TPOSR.ChurchRosserDepth.
Require Import Lambda.TPOSR.ChurchRosser.
Require Import Lambda.TPOSR.SubjectReduction.
Require Import Lambda.TPOSR.Unlab.
Require Import Lambda.TPOSR.TPOSR_trans.
Require Import Lambda.TPOSR.UnlabConv.

Require Import Lambda.Terms.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Russell.Types.

Set Implicit Arguments.

Ltac destruct_lab_inv c H :=
  destruct c ; try discriminate ; simpl in H ; inversion H ; subst.

Lemma russell_conv_eq : forall t u, Lambda.Reduction.conv (|t|) (|u|) ->
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

Lemma unlab_ctx_item : forall a x n,  
  item term x (unlab_ctx a) n -> 
  exists x', item lterm x' a n /\ (|x'|) = x.
Proof.
  induction a ; simpl ; intros.
  inversion H.
  inversion H.
  subst.
  exists a ; intuition ; auto.
  subst.
  destruct (IHa _ _ H3) ; destruct_exists.
  exists x0 ; intuition.
Qed.

Theorem russell_to_tposr : 
  (forall G M T, G |-- M : T ->
  exists3 G' M' T', unlab_ctx G' = G /\ (|M'|) = M /\ (|T'|) = T /\
  G' |-- M' -> M' : T') /\
  (forall G t u s, G |-- t >> u : s -> 
  exists3 G' t' u', unlab_ctx G' = G /\ (| t' |) = t /\ (| u' |) = u /\
  G' |-- t' >-> u' : s) /\
  (forall G, wf G -> exists G', unlab_ctx G' = G /\ tposr_wf G' /\
  (forall T n, Env.item_lift T G n -> 
  exists T', item_llift T' G' n /\ (|T'|) = T)).
Proof.
  apply double_typ_coerce_wf_mut with
  (P:= fun G M T => fun H : G |-- M : T =>
  exists3 G' M' T', unlab_ctx G' = G /\ (|M'|) = M /\ (|T'|) = T /\
  G' |-- M' -> M' : T')
  (P0 := fun G t u s => fun H : G |-- t >> u : s => 
  exists3 G' t' u', unlab_ctx G' = G /\ (| t' |) = t /\ (| u' |) = u /\
  G' |-- t' >-> u' : s)
  (P1 := fun G => fun H : wf G => exists G', unlab_ctx G' = G /\ tposr_wf G' /\
  (forall T n, Env.item_lift T G n -> 
  exists T', item_llift T' G' n /\ (|T'|) = T)) ; 
  simpl ; intros ; auto with coc ; destruct_exists.

  exists x (Srt_l prop) (Srt_l kind) ; split ; auto with coc.

  exists x (Srt_l set) (Srt_l kind) ; split ; auto with coc.

  (* Var *)
  destruct (H1 _ _ i) ; destruct_exists.
  exists x (Ref_l n) x0 ; split ; intuition ; auto with coc.

  (* Abs *)
  subst.
  destruct a0 ; try discriminate.
  destruct c1 ; try discriminate.
  destruct c0 ; try discriminate.
  simpl in H9, H6.
  destruct a ; inversion H9 ; inversion H6 ; inversion H0 ; inversion H1 ; subst.
  clear H6 H9.
  clear H0 H1.

  assert(tposr_wf a0).
  pose (wf_tposr H7).
  inversion t2.
  apply (wf_tposr H0).

  exists a0 (Abs_l b1 b) (Prod_l b1 b0) ; simpl ; intuition ; auto with coc.
  rewrite H8 ; auto.
  rewrite H8 ; auto.
  apply tposr_abs with s1 b0 s2 ; auto with coc.
  apply unlab_conv_ctx with a1 ; auto with coc.

  apply unlab_conv_ctx with (l :: a0) ; auto with coc.
  apply wf_cons with s1.
  apply unlab_conv_ctx with a1 ; auto with coc.
  simpl.
  rewrite H8 ; auto.

  apply unlab_conv_ctx with (l0 :: a) ; auto with coc.
  apply wf_cons with s1.
  apply unlab_conv_ctx with a1 ; auto with coc.
  destruct (validity H4) ; destruct_exists.
  rewrite H0 in H3.
  destruct b0 ; try discriminate.
  simpl in H3.
  inversion H3 ; subst.
  assumption.
  assert(tposr_term (l0 :: a) c b2) by eauto with coc ecoc.
  assert(l0 :: a |-- b0 -> b0 : s2).
  apply unlab_conv_ctx with (l :: a0) ; auto with coc.
  apply (wf_tposr H0).
  simpl ; auto.
  rewrite H8 ; rewrite H12.
  rewrite H11 ; rewrite H13 ; auto.
  assert(tposr_term (l0 :: a) b0 s2) by eauto with coc ecoc.
  pose (unlab_conv_sorted H1 H5 H3) ; destruct_exists.
  apply tposr_conv_l with c b2 ; auto with coc.
  simpl.
  rewrite H12 ; rewrite H11 ; rewrite H13 ; auto.

  (* App *)
  destruct_lab_inv c H2.
  exists a (App_l c2 b b0) (lsubst b0 c2) ; simpl ; intuition ; auto with coc.
  rewrite lab_subst ; auto.
  destruct (validity H3) ;destruct_exists ; try discriminate.
  pose (generation_prod H) ; destruct_exists.
  subst.
  apply tposr_app with c1 a2 b2 b3 ; auto with coc.
  eauto with coc ecoc.
  apply unlab_conv_ctx with a0 ; auto with coc.
  eauto with coc ecoc.
  apply tposr_conv_l with c0 b2 ; auto with coc.
  destruct (validity H6) ; destruct_exists.
  destruct c0 ; try discriminate.
  destruct_lab_inv c1 H8.
  apply tposr_eq_tposr.
  apply unlab_conv_ctx with a ; auto with coc.
  eauto with ecoc.
  eauto with coc ecoc.
  assert(a0 |-- c1 -> a2 : b2).
  apply unlab_conv_ctx with a ; eauto with coc ecoc. 
  assert(tposr_term a0 c0 b4) by eauto with coc ecoc.
  assert(tposr_term a0 c1 b2) by eauto with coc ecoc.
  pose (unlab_conv_sorted H11 H10 H8) ; destruct_exists.
  auto with coc.

  (* Pair *)
  destruct_lab_inv c2 H13.
  destruct_lab_inv c0 H7.
  exists a2 (Pair_l (Sum_l b2 b0) b1 b) (Sum_l b2 b0) ; simpl ; intuition ; auto with coc.

  assert(a1 |-- c1 >-> b2 : s1).
  destruct(validity H11) ; destruct_exists.
  subst c1.
  destruct b2 ; try discriminate.
  simpl in H10.
  injection H10.
  intros ; subst x.
  apply coerce_unlab_conv_ctx with a2 ; eauto with coc ecoc.
  assert(tposr_term a1 c1 b3) by eauto with coc ecoc.
  assert(a1 |-- b2 -> b2 : s1) by (apply unlab_conv_ctx with a2 ; eauto with coc ecoc).
  assert(tposr_term a1 b2 s1) by eauto with coc ecoc.
  destruct (unlab_conv_sorted H3 H9 H10).
  rewrite <- H12.
  eauto with coc ecoc.

  apply tposr_pair with s1 s2 s3 ; auto with coc.
  apply unlab_conv_ctx with a0 ; auto with coc.
  eauto with coc ecoc.
  apply unlab_conv_ctx with a1 ; auto with coc.
  eauto with coc ecoc.
  apply tposr_conv with c1 s1 ; auto with coc.

  assert(tposr_term a (lsubst b1 b0) s2).
  exists (lsubst b1 b0).
  apply unlab_conv_ctx with a2.
  eauto with coc ecoc.
  destruct a0 ; try discriminate.
  apply substitution_sorted with b2.
  apply unlab_conv_ctx with (l :: a0) ; auto with coc.
  eauto with coc ecoc.
  apply unlab_conv_ctx with a1 ; auto with coc.
  eauto with coc ecoc.
  apply tposr_conv with c1 s1 ; auto with coc.
  auto with coc.
  
  assert(exists s : sort, tposr_term a c s).
  destruct (validity H5) ; destruct_exists.
  destruct c ; try discriminate.
  injection H6 ; intros ; subst x.
  unfold subst in H4.
  pose (sym_eq H4).
  simpl in e.
  destruct (Lambda.Russell.Generation.inv_subst_sort _ _ _ e).
  destruct b1 ; try discriminate.
  simpl in H9.
  inversion H9 ; intros ; subst s4.
  pose (tposr_sort_kinded H11).
  exists kind.
  exists (Srt_l s0).
  rewrite e0 in H11.
  apply unlab_conv_ctx with a1 ; eauto with coc ecoc.
  rewrite H2 ; auto.
  destruct b0 ; try discriminate.
  simpl in H9.
  inversion H9 ; intros ; subst s4.
  exists s2.
  exists (Srt_l s0).
  destruct a0 ; try discriminate.
  inversion H1 ; subst.
  apply (tposr_sort_strenghten H8 (wf_tposr H5)).
  exists b3 ; exists a3 ; auto.
  destruct H6.
  
  rewrite <- lab_subst in H4.
  destruct (unlab_conv_sorted H6 H3 H4).
  apply unlab_conv_ctx with a ; auto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_conv with c x ; auto with coc.

  (* Prod *)
  destruct_lab_inv c0 H5.
  destruct_lab_inv c H2.
  exists a0 (Prod_l b0 b) (Srt_l s2).
  intuition ; auto.
  apply tposr_prod with s1 ; auto with coc.
  apply unlab_conv_ctx with a ; auto with coc.
  eauto with coc ecoc.

  (* Sum *)
  destruct_lab_inv c0 H5.
  destruct_lab_inv c H2.
  exists a0 (Sum_l b0 b) (Srt_l s3).
  intuition ; auto.
  apply tposr_sum with s1 s2 ; auto with coc.
  apply unlab_conv_ctx with a ; auto with coc.
  eauto with coc ecoc.
  
  (* Subset *)
  destruct_lab_inv c0 H5.
  destruct_lab_inv c H2.
  exists a0 (Subset_l b0 b) (Srt_l set).
  intuition ; auto.
  apply tposr_subset ; auto with coc.
  apply unlab_conv_ctx with a ; auto with coc.
  eauto with coc ecoc.

  (* Pi1 *)
  destruct_lab_inv c H1.
  exists a (Pi1_l (Sum_l c1 c2) b) c1.
  intuition ; auto.
  destruct (validity H2) ; destruct_exists ; try discriminate.
  pose (generation_sum H) ; destruct_exists.
  apply tposr_pi1 with b1 b2 x ; eauto with coc ecoc.

  (* Pi2 *)
  destruct_lab_inv c H1.
  exists a (Pi2_l (Sum_l c1 c2) b) (lsubst (Pi1_l (Sum_l c1 c2) b) c2).
  intuition ; auto.
  rewrite lab_subst ; auto.
  destruct (validity H2) ; destruct_exists ; try discriminate.
  pose (generation_sum H) ; destruct_exists.
  apply tposr_pi2 with b1 b2 x ; eauto with coc ecoc.

  (* Conv *)
  destruct_lab_inv c2 H10.
  destruct_lab_inv c1 H7.
  exists a2 b2 b1 ; intuition ; simpl ; auto with coc.
  apply tposr_conv with c3 s ; auto with coc.
  pose (coerce_refl_l H5).
  assert(tposr_term a b s) by eauto with coc.
  assert(tposr_term a c0 s) by eauto with coc ecoc.
  assert(a |-- b1 -> b1 : s).
  apply unlab_conv_ctx with a1 ; eauto with coc ecoc.
  rewrite H0 ; auto.
  assert(tposr_term a b1 s) by eauto with coc ecoc.
  assert(a |-- b2 -> b2 : c3).
  apply unlab_conv_ctx with a2 ; eauto with coc ecoc.
  destruct (unlab_conv_sorted H9 H13 H4).
  apply tposr_coerce_trans with c0 ; auto with coc.
  apply coerce_unlab_conv_ctx with a ; auto with coc.
  apply (wf_tposr H14).

  destruct (validity H14) ; destruct_exists.
  subst.
  destruct_lab_inv b H3.
  pose (tposr_coerce_sort_l H5).
  auto with coc.

  assert(a |-- c3 -> a3 : b3).
  apply unlab_conv_ctx with a2 ; eauto with coc ecoc.
  assert(tposr_term a c3 b3) by eauto with coc.
  pose (unlab_conv_sorted H H20 H3) ; destruct_exists.
  apply tposr_coerce_trans with b ; auto with coc.
  apply coerce_unlab_conv_ctx with a ; auto with coc. 
  eauto with coc ecoc.

  (* Coerce conv *)
  subst.
  destruct_lab_inv c H1.
  exists a b b ; intuition ; auto with coc.

  (* Coerce prod *)
  subst.
  destruct_lab_inv c5 H18.
  destruct_lab_inv c4 H15.
  destruct_lab_inv c2 H9.
  destruct_lab_inv c1 H6.
  
  exists a4 (Prod_l c6 b1) (Prod_l b4 c3) ; intuition ; auto with coc.
  apply tposr_coerce_prod with s ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply coerce_unlab_conv_ctx with a1 ; eauto with coc ecoc.
  apply tposr_coerce_env with (b4 :: a4).
  apply unlab_conv_ctx with a1 ; eauto with coc ecoc.
  eauto with coc ecoc.
  apply unlab_conv_ctx with a1 ; eauto with coc ecoc.

  (* Coerce sum *)
  subst.
  destruct_lab_inv c5 H18.
  destruct_lab_inv c4 H15.
  destruct_lab_inv c2 H9.
  destruct_lab_inv c1 H6.
  
  exists a4 (Sum_l b4 b1) (Sum_l c6 c3) ; intuition ; auto with coc.
  apply tposr_coerce_sum with s s' ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply coerce_unlab_conv_ctx with a1 ; eauto with coc ecoc.
  apply unlab_conv_ctx with a1 ; eauto with coc ecoc.
  apply tposr_coerce_env with (b4 :: a4).
  apply unlab_conv_ctx with a1 ; eauto with coc ecoc.
  eauto with coc ecoc.

  (* Coerce subset left *)
  subst.
  destruct_lab_inv c0 H2. 
  
  exists a0 (Subset_l b0 b) c1 ; intuition ; auto with coc.
  apply tposr_coerce_sub_l ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply unlab_conv_ctx with a ; eauto with coc ecoc.

  (* Coerce subset right *)
  subst.
  destruct_lab_inv c0 H2. 
  
  exists a0 b0 (Subset_l c1 b) ; intuition ; auto with coc.
  apply tposr_coerce_sub_r ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply unlab_conv_ctx with a ; eauto with coc ecoc.

  (* Coerce trans *)
  subst.
  destruct_lab_inv c6 H17.
  destruct_lab_inv c5 H14.
  destruct_lab_inv c4 H11.
  destruct_lab_inv c3 H8.

  exists a3 b3 b0 ; intuition ; auto with coc.
  pose (unlab_conv_ctx (wf_tposr H18) H15 (sym_eq H0)).
  pose (unlab_conv_ctx (wf_tposr H18) H12 (sym_eq H1)).
  pose (unlab_conv_ctx (wf_tposr H18) H9 (sym_eq H2)).
  destruct (coerce_refls H6).
  pose (unlab_conv_ctx (wf_tposr H18) H (sym_eq H3)).
  pose (unlab_conv_ctx (wf_tposr H18) H7 (sym_eq H3)).
  assert(tposr_term a3 c2 s) by eauto with coc.
  assert(tposr_term a3 b1 s) by eauto with coc.
  assert(tposr_term a3 b s) by eauto with coc.
  assert(tposr_term a3 b2 s) by eauto with coc.
  destruct (unlab_conv_sorted H10 H13 H5).
  destruct (unlab_conv_sorted H16 H19 H4).

  pose (russell_conv_eq c1 t4 t5).
  pose (russell_conv_eq c H18 t3).
  apply tposr_coerce_trans with b2 ; auto with coc.
  apply tposr_coerce_trans with b ; auto with coc.
  apply tposr_coerce_trans with b1 ; auto with coc.
  apply tposr_coerce_trans with c2 ; auto with coc.
  apply coerce_unlab_conv_ctx with a ; auto with coc.
  eauto with coc ecoc.

  (* Wf *)
  intros.
  exists (nil (A:=lterm)).
  intuition ; auto.
  inversion H.
  inversion H1.

  destruct_lab_inv c H1.
  exists (b :: a).
  intuition.
  eauto with coc ecoc.

  inversion H.
  subst.
  inversion H3.
  subst.
  exists (llift 1 b).
  intuition ; auto with coc.
  exists b ; auto.
  eauto with coc.
  apply lab_lift.
  subst.
  change (|b| :: unlab_ctx a) with (unlab_ctx (b :: a)) in H3.
  destruct (unlab_ctx_item _ H3) ; destruct_exists.
  exists (llift (S (S n0)) x0).
  intuition ; auto.
  exists x0 ; auto.
  rewrite lab_lift.
  rewrite H4 ; auto.
Qed.

Corollary type_russell_tposr :
  forall G M T, G |-- M : T ->
  exists3 G' M' T', unlab_ctx G' = G /\ (|M'|) = M /\ (|T'|) = T /\
  G' |-- M' -> M' : T'.
Proof (proj1 russell_to_tposr).

Corollary coerce_russell_tposr :
  forall G t u s, G |-- t >> u : s -> 
  exists3 G' t' u', unlab_ctx G' = G /\ (| t' |) = t /\ (| u' |) = u /\
  G' |-- t' >-> u' : s.
Proof (proj1 (proj2 russell_to_tposr)).

Corollary wf_russell_tposr :
  forall G, wf G -> exists G', unlab_ctx G' = G /\ tposr_wf G'.
Proof.
  destruct (russell_to_tposr) ; destruct_exists.
  intros.
  pose (H1 G H2) ; destruct_exists ; auto.
  exists x ; intuition.
Qed.
