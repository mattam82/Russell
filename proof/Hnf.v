Require Import Lambda.Terms.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Env.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Definition redex (x : term) :=
  match x with
  App (Abs _ _) _ => True
  | Pi1 (Pair _ _ _) => True
  | Pi2 (Pair _ _ _) => True
  | _ => False
  end.

Inductive hnf : term -> term -> Prop :=
  | hnf_beta : forall T e v, 
    forall H, hnf (subst v e) H ->
    hnf (App (Abs T e) v) H
  | hnf_pi1 :  forall T x y, 
    forall H, hnf x H -> 
    hnf (Pi1 (Pair T x y)) H
  | hnf_pi2 :  forall T x y, 
    forall H, hnf y H -> 
    hnf (Pi2 (Pair T x y)) H
  | hnf_other : forall x, ~ (redex x) -> hnf x x.

Lemma hnf_prod : forall U V, hnf (Prod U V) (Prod U V).
Proof.
  intros.
  apply hnf_other.
  red ; intros.
  simpl in H.
  auto.
Qed.

Lemma hnf_function : forall x y z, hnf x y -> hnf x z -> y = z.
Proof.
  induction 1 ; simpl ; intros.

  inversion H1 ; subst ; auto.
  elim H2.
  simpl.
  auto.

  inversion H1 ; subst ; auto.
  elim H2.
  simpl.
  auto.

  inversion H1 ; subst ; auto.
  elim H2.
  simpl.
  auto.

  inversion H0.
  subst.
  elim H ; simpl ; auto.

  subst.
  elim H ; simpl ; auto.

  subst.
  elim H ; simpl ; auto.

  auto.
Qed.

Lemma hnf_







