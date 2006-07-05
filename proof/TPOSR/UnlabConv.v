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
Require Import Lambda.TPOSR.UnicityOfSorting.
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

Hint Unfold tposr_term tposr_term_depth : coc.
Hint Unfold equiv_sort : coc.
Hint Resolve conv_env : coc.

Lemma tposr_term_conv_env : forall e t T, tposr_term e t T ->
  forall f, conv_in_env e f -> tposr_term f t T.
Proof.
  unfold tposr_term ; intros ; destruct_exists.
  exists x ; eauto with coc ecoc.
Qed.

Hint Resolve tposr_term_conv_env : coc.

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
  
Admitted.

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
  apply wf_cons with A' s.
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
  assert(G |-- a0 -> A'0 : Srt_l s0).
  apply conv_env_full with D ; auto.
  apply conv_env_full_sym ; auto.
  apply wf_cons with A'0 s0 ; auto.

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
