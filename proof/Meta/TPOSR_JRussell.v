Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.Tactics.

Require Import Lambda.JRussell.Types.
Require Import Lambda.JRussell.Basic.
Require Import Lambda.JRussell.Coercion.
Require Import Lambda.JRussell.Generation.
Require Import Lambda.JRussell.Thinning.
Require Import Lambda.JRussell.Substitution.
Require Import Lambda.JRussell.Validity.

Require Import Lambda.Meta.JRussell_Russell.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Unlab.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Set Implicit Arguments.

Lemma item_unlab : forall n t e, item lterm t e n -> item term (|t|) (unlab_ctx e) n.
Proof.
  induction n ; simpl ; intros ; auto.
  inversion H.
  simpl.
  constructor.
  
  inversion H.
  simpl.
  constructor.
  apply IHn ; auto.
Qed.

Theorem unlab_sound  : 
  (forall e u v T, e |-- u -> v : T -> 
  (unlab_ctx e) |-= (|u|) = (|v|) : (|T|)) /\
  (forall e, tposr_wf e -> 
  (unlab_ctx e) |-= Srt prop : Srt kind /\
  (unlab_ctx e) |-= Srt set : Srt kind /\
  (forall A n, item_llift A e n -> 
  (unlab_ctx e) |-= Ref n : (|A|))) /\
  (forall e u v s, e |-- u ~= v : s ->
  (unlab_ctx e) |-= (|u|) = (|v|) : Srt s) /\
  (forall e u v s, e |-- u >-> v : s ->
  (unlab_ctx e) |-= (|u|) >> (|v|) : s).
Proof.
  apply ind_tposr_wf_eq with 
  (P := fun e u v T =>  fun H : e |-- u -> v : T =>
  (unlab_ctx e) |-= (|u|) = (|v|) : (|T|))
  (P0 := fun e => fun H : tposr_wf e =>
  (unlab_ctx e) |-= Srt prop : Srt kind /\
  (unlab_ctx e) |-= Srt set : Srt kind /\
  (forall A n, item_llift A e n -> 
  (unlab_ctx e) |-= Ref n : (|A|)))
  (P1 := fun e u v s => fun H : e |-- u ~= v : s =>
  (unlab_ctx e) |-= (|u|) = (|v|) : Srt s) 
  (P2 := fun e u v s => fun H : e |-- u >-> v : s =>
  (unlab_ctx e) |-= (|u|) >> (|v|) : s) 
  ; simpl ; intros ; auto with coc.

  intuition.

  intuition.

  intuition.

  apply jeq_prod with s1 ; auto with coc.

  apply jeq_abs with s1 s2 ; auto with coc.
  apply (jeq_type_l H0).

  rewrite lab_subst.
  apply jeq_app with (|A|) ; auto.

  do 2 rewrite lab_subst.
  pose (jeq_type_l H).
  pose (jeq_type_l H0).
  pose (jeq_type_l H1).
  pose (jeq_type_l H2).
  
  apply jeq_trans with (subst (|N |) (|M |)) ; auto with coc.
  apply jeq_beta with s1 s2 ; auto with coc.
  
  apply jeq_subst_par with (|A|); auto with coc.

  apply jeq_conv with (|A|) s ; auto with coc.

  apply jeq_conv with (|B|) s ; auto with coc.

  apply jeq_subset ; auto with coc.

  apply jeq_sum  with s1 s2 ; auto with coc.
  
  rewrite lab_subst in H2.
  apply jeq_pair with s1 s2 s3 ; auto with coc.
 
  apply jeq_pi1 with (|B|) ; auto with coc.

  pose (jeq_type_l H).
  pose (jeq_type_l H0).
  pose (jeq_type_l H1).
  pose (coerce_sort_l H2).
  pose (coerce_sort_l H3).
  pose (generation_pair t6).
  destruct_exists.
  pose (jeq_type_r H1).
  inversion H4.
  pose (generation_pair t9) ; destruct_exists.
  apply jeq_trans with (Pi1 (Pair (Sum (|A'|) (|B'|)) (|u'|) (|v'|))) ; auto with coc.
  apply jeq_conv with (|A|) s1 ; auto with coc.
  apply jeq_pi1 with (|B|) ; auto with coc.
  apply jeq_conv with (|A'|) s1 ; auto with coc.
  inversion H11.
  apply jeq_pi1_red with s1 s2 s3 ; auto with coc.
  apply (jeq_type_r H).
  pose (jeq_type_r H0).
  apply type_conv_env with ((|A|) :: unlab_ctx e) ; auto with coc.
  apply conv_env_hd with s1 ; auto with coc.
  rewrite H21 ; assumption.
  rewrite H22 ; assumption.
  apply coerce_trans with (|A|) ; auto with coc.

  rewrite lab_subst.
  simpl.
  apply jeq_pi2 with (|A|) ; auto with coc.

  pose (jeq_type_l H).
  pose (jeq_type_r H).
  pose (jeq_type_l H0).
  pose (jeq_type_r H0).
  pose (jeq_type_l H1).
  pose (jeq_type_r H1).
  pose (generation_pair t8).
  pose (generation_pair t9).
  destruct_exists.
  inversion H5.
  inversion H4.
  rewrite lab_subst.
  apply jeq_trans with (Pi2 (Pair (Sum (|A'|) (|B'|)) (|u'|) (|v'|))) ; auto with coc.
  simpl. 
  apply jeq_pi2 with (|A|) ; auto with coc.
  simpl.
  subst.
  apply jeq_conv with (Sum (|A|) (|B|)) s3.
  auto with coc.
  apply coerce_sum with x6 s2 ; auto with coc.
  apply coerce_coerce_env with ((|A''|) :: unlab_ctx e) ; auto with coc.
  apply coerce_env_hd with s1 ; auto with coc.
  apply typ_coerce_env with ((|A''|) :: unlab_ctx e) ; auto with coc.
  eauto with coc.
  apply coerce_env_hd with s1 ; auto with coc.
  rewrite (jeq_unique_sort _ _ _ _ H12 (coerce_sort_r H2)).
  assumption.
  rewrite (jeq_unique_sort _ _ _ _ H12 (coerce_sort_r H2)).
  assumption.

  apply jeq_conv with (subst (|u'|) (|B'|)) s2 ; auto with coc.
  apply jeq_pi2_red with s1 s2 s3 ; auto with coc.
  apply type_conv_env with ((|A|) :: unlab_ctx e) ; auto with coc.
  apply conv_env_hd with s1 ; auto with coc.
  rewrite H21 ; assumption.
  rewrite H22 ; assumption.

  apply coerce_trans with (subst (|u'|) (|B|)) ; auto with coc.
  apply substitution_coerce with x ; auto with coc.
  subst.
  apply coerce_sym.
  apply coerce_conv.
  apply jeq_conv_env with ((|A|) :: unlab_ctx e) ; auto with coc.
  apply conv_env_hd with s1 ; auto with coc.
  
  apply coerce_trans with (subst (|u'|) (|B''|)) ; auto with coc.
  apply substitution_coerce with x ; auto with coc.
  rewrite <- H21.
  apply coerce_coerce_env with (|A''| :: unlab_ctx e) ; auto with coc.
  apply coerce_env_hd with s1 ; auto with coc.
  apply coerce_trans with (|A|) ; auto with coc.
  apply coerce_conv.
  change (Srt s2) with (subst (|u'|) (Srt s2)).
  apply functionality with x ; auto with coc.
  apply jeq_sym.
  simpl.
  rewrite <- H21.
  apply jeq_conv with (|A|) s1 ; auto with coc.
  apply jeq_trans with (Pi1 (Pair (Sum (|A'|) (|B'|)) (|u'|) (|v'|))) ; auto with coc.
  apply jeq_pi1 with (|B|) ; auto with coc.
  apply jeq_conv with (|A'|) s1 ; auto with coc.
  apply jeq_pi1_red with s1 s2 s3 ; auto with coc.
  apply type_conv_env with ((|A|) :: unlab_ctx e) ; auto with coc.
  apply conv_env_hd with s1 ; auto with coc.
  rewrite H21 ; assumption.
  rewrite H22 ; assumption.
  rewrite <- H21.
  apply typ_coerce_env with ((|A''|) :: unlab_ctx e) ; auto with coc.
  apply (coerce_sort_l H3).
  apply coerce_env_hd with s1 ; auto with coc.
  apply coerce_trans with (|A|) ; auto with coc.

  split ; auto with coc.
  split ; auto with coc.
  intros.
  inversion H.
  inversion H1.

  split ; auto with coc.
  apply sort_judgement_empty_env ; auto with coc.
  apply consistent_cons with s ; auto with coc.
  apply (jeq_consistent H).
  apply (jeq_type_l H).

  split.
  apply sort_judgement_empty_env ; auto with coc.
  apply consistent_cons with s ; auto with coc.
  apply (jeq_consistent H).
  apply (jeq_type_l H).

  intros.
  inversion H0.
  rewrite H1.
  rewrite lab_lift.
  apply (item_ref_lift).
  induction n.
  inversion H2.
  constructor.
  constructor.
  inversion H2.
  apply (item_unlab H4).
  
  apply consistent_cons with s.
  apply (jeq_consistent H).
  apply (jeq_type_l H).

  apply jeq_trans with (|X|) ; auto.

  apply coerce_prod with s ; eauto with coc.

  apply coerce_sum with s s' ; eauto with coc.

  apply coerce_sub_l ; eauto with coc.

  apply coerce_sub_r ; eauto with coc.

  apply coerce_trans with (|B|) ; eauto with coc.
Qed.

Corollary unlab_sound_type : forall e u v T, e |-- u -> v : T -> 
  (unlab_ctx e) |-= (|u|) = (|v|) : (|T|).
Proof (proj1 (unlab_sound)).

Corollary unlab_sound_wf :
  (forall e, tposr_wf e -> 
  (unlab_ctx e) |-= Srt prop : Srt kind /\
  (unlab_ctx e) |-= Srt set : Srt kind /\
  (forall A n, item_llift A e n -> 
  (unlab_ctx e) |-= Ref n : (|A|))).
Proof (proj1 (proj2 (unlab_sound))).

Corollary unlab_sound_eq : forall e u v s, e |-- u ~= v : s -> 
  (unlab_ctx e) |-= (|u|) = (|v|) : Srt s.
Proof (proj1 (proj2 (proj2 (unlab_sound)))).

Corollary unlab_sound_coerce : forall e u v s, e |-- u >-> v : s -> 
  (unlab_ctx e) |-= (|u|) >> (|v|) : s.
Proof (proj2 (proj2 (proj2 (unlab_sound)))).


