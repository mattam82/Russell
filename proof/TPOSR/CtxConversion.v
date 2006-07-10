Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Basic.
Require Import Lambda.TPOSR.CtxCoercion.
Require Import Lambda.TPOSR.RightReflexivity.
Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Inductive conv_in_env : lenv -> lenv -> Prop :=
  | conv_env_hd : forall e t u s, e |-- t ~= u : s -> 
	conv_in_env (t :: e) (u :: e)
  | conv_env_tl :
      forall e f t, conv_in_env e f -> conv_in_env (t :: e) (t :: f).

Hint Resolve conv_env_hd conv_env_tl: coc.

Lemma conv_in_env_coerce_in_env : forall e f, conv_in_env e f -> tposr_wf e -> coerce_in_env e f.
Proof.
  induction 1 ; simpl ; intros ; eauto with coc.
  inversion H0.
  subst.
  pose (wf_tposr H2).
  pose (IHconv_in_env t0).
  apply coerce_env_tl ; auto.
  apply wf_cons with s.
  apply tposr_coerce_env with e ; auto.
Qed.  
   
Hint Resolve conv_in_env_coerce_in_env : coc.

Lemma conv_env :
  (forall e t u T, e |-- t -> u : T -> 
  forall f, conv_in_env e f -> f |-- t -> u : T).
Proof.
  intros.
  apply tposr_coerce_env with e ; eauto with coc ecoc.
Qed.

Corollary eq_conv_env : 
  (forall e t u s, e |-- t ~= u : s -> 
  forall f, conv_in_env e f -> f |-- t ~= u : s).
Proof.
  intros.
  apply eq_coerce_env with e ; eauto with coc ecoc.
Qed.

Corollary coerce_conv_env : 
  (forall e t u s, e |-- t >-> u : s -> 
  forall f, conv_in_env e f -> f |-- t >-> u : s).
Proof.
  intros.
  apply coerce_coerce_env with e ; eauto with coc ecoc.
Qed.

Lemma conv_in_env_sym : forall e f, conv_in_env e f -> conv_in_env f e.
Proof.
  induction 1 ; eauto with coc ecoc.
Qed.

Hint Resolve conv_in_env_sym : coc.
