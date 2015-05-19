Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.PreCtxCoercion.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.RightReflexivity.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Inductive coerce_in_env : lenv -> lenv -> Prop :=
  | coerce_env_hd : forall e t u s, e |-- t >-> u : s -> 
	coerce_in_env (u :: e) (t :: e)
  | coerce_env_tl :
        forall e f t, tposr_wf (t :: f) -> coerce_in_env e f -> coerce_in_env (t :: e) (t :: f).

Hint Resolve coerce_env_hd coerce_env_tl: coc.

Lemma coerce_in_env_pre : forall e f, coerce_in_env e f -> pre_coerce_in_env e f.
Proof.
  induction 1 ; simpl ; intros ; eauto with coc.
  inversion H.
  apply pre_coerce_env_tl with s ; auto.
Qed.

Lemma tposr_coerce_env : forall e t u T, e |-- t -> u : T -> 
  forall f, coerce_in_env e f -> f |-- t -> u : T.
Proof.
  intros.
  eapply tposr_pre_coerce_env ; eauto with coc.
  apply coerce_in_env_pre ; auto.
Qed.

Lemma eq_coerce_env : forall e T U s, e |-- T ~= U : s -> 
  forall f, coerce_in_env e f -> f |-- T ~= U : s.
Proof.
  intros.
  eapply eq_pre_coerce_env ; eauto with coc.
  apply coerce_in_env_pre ; auto.
Qed.

Lemma coerce_coerce_env : forall e T U s, e |-- T >-> U : s -> 
  forall f, coerce_in_env e f -> f |-- T >-> U : s.
Proof.
  intros.
  eapply coerce_pre_coerce_env ; eauto with coc.
  apply coerce_in_env_pre ; auto.
Qed.

Corollary tposrp_coerce_env : forall e t u T, e |-- t -+> u : T -> 
  forall f, coerce_in_env e f -> f |-- t -+> u : T.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  apply tposrp_tposr.
  eapply tposr_coerce_env ; eauto with coc.
  apply tposrp_trans with X ; auto with coc.
Qed.

Hint Resolve tposr_coerce_env eq_coerce_env coerce_coerce_env : ecoc.

Lemma coerce_in_env_sym : forall e f, coerce_in_env e f -> coerce_in_env f e.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  apply coerce_env_tl ; auto with coc.
  inversion H.
  subst.
  apply wf_cons with s ; eauto with coc ecoc.
Qed.

Hint Resolve coerce_in_env_sym : coc.

Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.PreSubstitutionTPOSR.

Lemma substitution_coerce_tposrp : 
  forall e d d' t, e |-- d -+> d' : t -> 
  forall u v s, t :: e |-- u >-> v : s -> e |-- (lsubst d u) >-> (lsubst d' v) : s.
Proof.
  induction 1 ; intros.
  
  apply substitution_tposr_coerce with Z ; eauto with coc.

  apply tposr_coerce_trans with (lsubst X u) ; auto.
  apply IHtposrp1.
  apply tposr_coerce_conv ; apply tposr_eq_tposr ; auto.
  apply (coerce_refl_l H1).
Qed.

