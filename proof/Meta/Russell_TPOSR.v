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
Require Import Lambda.Russell.Types.

Set Implicit Arguments.

Ltac destruct_lab_inv c H :=
  destruct c ; try discriminate ; simpl in H ; inversion H ; subst.

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
  
  Focus 7.
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
Admitted.  

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
