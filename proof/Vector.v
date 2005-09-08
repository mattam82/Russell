Require Import Coq.Arith.Arith.
Parameter A : Set.

Inductive vec : nat -> Set :=
  | vnil : vec 0
  | vcons : forall n, A -> vec n -> vec (S n).

Definition hd : forall n, n > 0 -> vec n -> A.
Proof.
  intros n H v ; induction v.
  elim (gt_irrefl _ H).
  assumption.
Defined.

Definition tl : forall n, n > 0 -> vec n -> vec (pred n).
Proof.
  intros n H v ; induction v.
  elim (gt_irrefl _ H).
  simpl.
  assumption.
Defined.  

Set Implicit Arguments.

Definition nth : forall n m, m < n -> vec n -> A.
Proof.
  intros.
  induction H0.
  elim (lt_n_O _ H).
  assumption.
Defined.

Require Import Omega.

Definition vapp : forall n m, vec n -> vec m -> vec (n + m).
Proof.
  intros.
  induction H.
  simpl.
  assumption.

  pose (vcons (n + m) a IHvec).
  assert(S (n + m) = S n + m).
  simpl.
  reflexivity.
  rewrite <- H1.
  exact v.
Defined.

Require Import Eqdep.

Definition vec_plus : forall n m, forall t : vec (n + m), 
  exists t' : vec (m + n), eq_dep nat vec (n + m) t (m + n) t'.
Proof.
  intros.
  rewrite plus_comm.
  exists t.
  auto.
Qed.

Require Import JMeq.

Lemma eq_dep_vnil : forall n, forall a : vec n,
  n = 0 -> eq_dep nat vec n a 0 vnil.
Proof.
  intros.
  
  simpl.
  induction a.
  auto.

  discriminate.
Qed.

Lemma eq_vnil : forall v : vec 0, v = vnil.
Proof.
  intros.
  apply eq_dep_eq with (P := vec).
  apply eq_dep_vnil.
  auto.
Qed.

Lemma vapp_vnil_l : forall n, forall v : vec n,
  vapp vnil v = v.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma vapp_vnil_dep_l : forall n, forall v : vec n,
  eq_dep nat vec n (vapp vnil v) n v.
Proof.
  intros.
  simpl.
  apply eq_dep_intro.
Qed.
  
Lemma vapp_vnil_dep_r : forall n, forall v : vec n,
  eq_dep nat vec (n + 0) (vapp v vnil) n v.
Proof.
  intros.
  induction v.
  simpl ; auto.

  simpl.

  pose (proj2 (equiv_eqex_eqdep nat vec (n + 0) n (vapp v vnil) v) IHv).
  dependent rewrite -> e.
  simpl.
  auto.
Qed.

Infix ":::" := vcons (at level 60, right associativity) : vector_scope.
Infix "+++" := vapp (right associativity, at level 60) : vector_scope.

(* 
 Local Variables:
 coq-prog-name: "coqtop.opt -emacs -R . CCP"
 End:
*)
