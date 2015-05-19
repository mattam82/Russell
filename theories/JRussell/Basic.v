Require Import Lambda.Terms.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Env.
Require Import Lambda.JRussell.Types.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Lemma lift_sort : forall n t s, lift n t = Srt s -> t = Srt s.
Proof.
  induction t ; simpl ; intros ; try discriminate.
  simpl in H ; auto.
Qed.

Lemma left_not_kind : forall G t T, G |-= t : T -> t <> Srt kind.
Proof.
  induction 1 ; intros ; unfold not ; intros ; try discriminate ; auto with coc.
  apply IHtyp1.
  pose (lift_sort 1 _ H1).
  assumption.
Qed.

Lemma coerce_prop_prop : nil |-= Srt prop >> Srt prop : kind.
Proof.
  intros.
  auto with coc.
Qed.

Lemma coerce_set_set : nil |-= Srt set >> Srt set : kind.
Proof.
  intros.
  auto with coc.
Qed.

Lemma coerce_is_prop : forall s, is_prop s -> nil |-= Srt s >> Srt s : kind.
Proof.
  intros.
  induction H ;
  rewrite H ; auto with coc.
Qed.

Lemma consistency_ind :
  (forall e t T, e |-= t : T -> consistent e) /\
  (forall e T U s, e |-= T >> U : s -> consistent e) /\
  (forall e U V T, e |-= U = V : T -> consistent e).
Proof.
  apply typ_coerce_jeq_ind with
  (P:=fun e t T => fun H: e |-= t : T => consistent e)
  (P1 := fun e U V T => fun H : e |-= U = V : T => consistent e)
  (P0 := fun e T U s => fun H : e |-= T >> U : s => consistent e) ;
  simpl ; intros ; auto with coc.

  apply consistent_cons with s ; auto with coc.
  apply consistent_cons with s ; auto with coc.

  apply consistent_cons with s' ; auto with coc.
  apply consistent_cons with s ; auto with coc.
Qed.

Lemma typ_consistent : forall e t T, e |-= t : T -> consistent e.
Proof (proj1 consistency_ind).

Lemma jeq_consistent : forall e U V T, e |-= U = V : T -> consistent e.
Proof (proj2 (proj2 consistency_ind)).

Lemma coerce_consistent : forall e T U s, e |-= T >> U : s -> consistent e.
Proof (proj1 (proj2 consistency_ind)).



Hint Resolve coerce_prop_prop coerce_set_set coerce_is_prop : coc.
Hint Resolve lift_sort left_not_kind : coc.
