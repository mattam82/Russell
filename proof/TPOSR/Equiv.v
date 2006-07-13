Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Basic.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.CtxConversion.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.TypesDepth.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Definition eq_kind U V := U = Srt_l kind /\ V = Srt_l kind.

Hint Unfold eq_kind : coc.

Lemma eq_kind_sym : forall U V, eq_kind U V -> eq_kind V U.
Proof.
  unfold eq_kind ; intuition.
Qed.

Hint Resolve eq_kind_sym : coc.

Lemma eq_kind_typ_l_l : forall U V, eq_kind U V -> forall e x1 x2, ~ (e |-- U -> x1 : x2).
Proof.
  intros.
  destruct H.
  rewrite H.
  red ; intros.
  apply (tposr_not_kind H1).
Qed.

Lemma eq_kind_typ_r_l : forall U V, eq_kind U V -> forall e x1 x2, ~ (e |-- V -> x1 : x2).
Proof.
  intros.
  pose (eq_kind_sym H).
  apply eq_kind_typ_l_l with U ; auto.
Qed.

Lemma eq_kind_typ_l_r : forall U V, eq_kind U V -> forall e x1 x2, ~ (e |-- x1 -> U : x2).
Proof.
  intros.
  red ; intros.
  pose (refl_r H0).
  elim eq_kind_typ_l_l with U V e U x2 ; auto.
Qed.

Lemma eq_kind_typ_r_r : forall U V, eq_kind U V -> forall e x1 x2, ~ (e |-- x1 -> V : x2).
Proof.
  intros.
  pose (eq_kind_sym H).
  apply eq_kind_typ_l_r with U ; auto.
Qed.

Hint Resolve eq_kind_typ_l_l eq_kind_typ_l_r eq_kind_typ_r_l eq_kind_typ_r_r : coc.

Definition equiv e A B := (eq_kind A B \/ exists s, e |-- A >-> B : s).
Definition equiv_sort e A B s := e |-- A >-> B : s.

Definition tposr_eq_equiv : forall e A B s, e |-- A ~= B : s -> equiv e A B.
intros.
right.
exists s. 
apply tposr_coerce_conv.
assumption.
Defined.

Hint Resolve tposr_eq_equiv : ecoc.

Definition tposr_coerce_equiv : forall e A B s, e |-- A >-> B : s -> equiv e A B.
intros.
right.
exists s. 
assumption.
Defined.

Hint Resolve tposr_coerce_equiv : ecoc.

Hint Unfold eq_kind equiv : coc.

Lemma tposr_equiv_l : forall e A B, equiv e A B -> forall M N, 
  e |-- M -> N : A -> e |-- M -> N : B.
Proof.
  destruct 1 ; intros.
  destruct H.
  rewrite H in H0 ; rewrite H1 ; assumption.
  destruct H.
  apply tposr_conv with A x  ; auto.
Qed. 

Lemma tposrp_equiv_l : forall e A B, equiv e A B -> forall M N, 
  e |-- M -+> N : A -> e |-- M -+> N : B.
Proof.
  induction 2 ; simpl ; intros.
  apply tposrp_tposr.
  apply tposr_equiv_l with Z ; auto.
  apply tposrp_trans with X ; auto with coc.
Qed.

Lemma tposr_equiv_r : forall e A B, equiv e A B -> forall M N, 
  e |-- M -> N : B -> e |-- M -> N : A.
Proof.
  destruct 1 ; intros.
  destruct H.
  rewrite H ; rewrite H1 in H0 ; assumption.
  destruct H.
  apply tposr_conv with B x ; auto with coc.
Qed. 

Lemma tposrd_unique_sort : forall G M M' M'' s s' n m, G |-- M -> M' : Srt_l s [n] ->
  G |-- M -> M'' : Srt_l s' [m] -> s = s'.
Proof.
  intros.
  pose (tposrd_tposr_type H).
  pose (tposrd_tposr_type H0).
  apply (unique_sort t t0).
Qed.

Lemma tposr_unique_sort_right : forall G A B C s s', G |-- A -> C : Srt_l s ->
  G |-- B -> C : Srt_l s' -> s = s'.
Proof.
  intros.
  pose (refl_r H).
  pose (refl_r H0).
  apply unique_sort with G C C C ; auto with coc.
Qed.

Lemma tposr_eq_unique_sort_right : forall G A B C s s', G |-- A ~= C : s ->
  G |-- B ~= C : s' -> s = s'.
Proof.
  intros.
  apply eq_unique_sort with G C A B ; auto with coc.
Qed.

Lemma tposr_coerce_unique_sort_right : forall G A B C s s', G |-- A >-> C : s ->
  G |-- B >-> C : s' -> s = s'.
Proof.
  intros.
  apply coerce_unique_sort with G C A B ; auto with coc.
Qed.

Lemma equiv_sort_trans : forall G A B C s s', equiv_sort G A C s -> equiv_sort G B C s' -> equiv_sort G A B s.
Proof.
  unfold equiv_sort.
  intros.
  pose (tposr_coerce_unique_sort_right H H0).
  rewrite <- e in H0.
  apply tposr_coerce_trans with C ; auto with coc.
Qed.

Lemma equiv_trans : forall G A B C, equiv G A C -> equiv G B C -> equiv G A B.
Proof.
  unfold equiv.
  intros.
  destruct H ; destruct H0 ; intuition ; destruct_exists.

  destruct H ; destruct H0.
  rewrite H ; rewrite H0 ; left ; unfold eq_kind ; intuition. 
  
  destruct H.
  rewrite H1 in H0.
  pose (coerce_refl_r H0).
  elim (tposr_not_kind t) ; auto.

  destruct H0.
  rewrite H1 in H.
  elim (tposr_not_kind (coerce_refl_r H)).

  right.

  pose (tposr_coerce_unique_sort_right H H0).
  exists x.
  apply tposr_coerce_trans with C ; auto with coc.
  rewrite <- e ; auto.
Qed.

Lemma equiv_coerce : forall e A s, e |-- A -> A : Srt_l s ->
  forall B, equiv e A B -> e |-- A >-> B : s.
Proof.
  intros.
  destruct H0.
  destruct H0.
  rewrite H0 in H.
  elim (tposr_not_kind H).
  destruct H0.

  rewrite (unique_sort H (coerce_refl_l H0)) ; assumption.
Qed.

Lemma equiv_sym : forall G A B, equiv G A B -> equiv G B A.
Proof.
  destruct 1.
  left ; intuition.
  destruct H ; intuition.
  right ; exists x ; auto with coc.
Qed.

Hint Resolve equiv_sym : coc.

Require Import Lambda.TPOSR.Thinning.

Lemma equiv_sort_weak : forall G s s', equiv G s s' -> forall a, tposr_wf (a :: G) -> equiv (a :: G) s s'.
Proof.
  induction 1.
  intros.
  left.
  assumption.

  intros.
  destruct_exists.
  right.
  exists x.
  change (Srt_l s) with (llift 1 (Srt_l s)).
  change (Srt_l s') with (llift 1 (Srt_l s')).
  apply thinning_coerce ; auto.
Qed.

Lemma inv_llift_sort : forall t s n, llift n t = Srt_l s -> t = Srt_l s.
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold llift in H ; simpl in H.
auto.
Qed.

Lemma inv_subst_sort : forall t t' n s, lsubst_rec t t' n = Srt_l s -> 
  t = Srt_l s \/ t' = Srt_l s.
Proof.
  induction t' ;  simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  generalize H.
  elim (lt_eq_lt_dec n0 n).
  intros a ; case a ; clear a ; intros ; try discriminate ; auto.
  left.
  exact (inv_llift_sort _ _ H0).

  intros.
  discriminate.
Qed.
