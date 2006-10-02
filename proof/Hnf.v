Require Import Lambda.Terms.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Env.

Set Implicit Arguments.

Implicit Types i k m n : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Fixpoint redex (x : term) :=
  match x with
  App (Abs _ _) _ => True
  | Pi1 (Pair _ _ _) => True
  | Pi2 (Pair _ _ _) => True
  | App x y => redex x 
  | Pi1 x => redex x
  | Pi2 x => redex x
  | _ => False
  end.

Axiom hnf_measure : term -> nat.

Program Fixpoint hnf (x : term) { measure x hnf_measure } : term :=
  match x with
  | App x y => 
    match hnf x with
    | Abs T v => hnf (subst y v)
    | h => App h y
    end
  | Pi1 x =>
    match hnf x with
    | Pair T u v => hnf u
    | h => Pi1 h
    end
  | Pi2 x =>
    match hnf x with
    | Pair T u v => hnf u
    | h => Pi2 h
    end
  | x => x
  end.

Obligation 1.
  simpl ; subst ; intros.
  subst.


Inductive hnf : term -> term -> Prop :=
  | hnf_beta : forall x, forall T e v, 
    (hnf x (Abs T e) -> 
    forall H, hnf (subst v e) H ->
    hnf (App x v) H) ->
    
  | hnf_pi1 :  forall p T x y, 
    hnf p (Pair T x y) ->
    forall H, hnf x H -> 
    hnf (Pi1 p) H
  | hnf_pi2 :  forall p T x y, hnf p (Pair T x y) ->
    forall H, hnf y H -> hnf (Pi2 p) H
  | hnf_other : forall x, ~ (exists y, hnf x y /\ y <> x) -> hnf x x.

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

Lemma hnf_total : forall x, exists y, hnf x y.
Proof.
  induction x.

  exists (Srt s) ; apply hnf_other ; simpl ; auto.

  exists (Ref n) ; apply hnf_other ; simpl ; auto.

  exists (Abs x1 x2) ; apply hnf_other ; simpl ; auto.

  (* App *)
  induction IHx1.
  induction x1.
  exists (Srt s) ; apply hnf_other ; simpl ; auto.







