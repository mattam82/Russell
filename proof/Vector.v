Require Import Coq.Arith.Arith.

Section Vector.
  Variable A : Set.
  
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
    
  Lemma Sm_n_lt_m_n : forall n m, S n < m -> n < m.
  Proof.
    induction n ; simpl ; auto with arith.
  Qed.

  Definition nth : forall m n, m < n -> vec n -> A.
  Proof.
    induction m ; intros.
    induction H0.
    elim (lt_n_O _ H).
    assumption.

    induction H0.
    elim (lt_n_O _ H).
    apply (IHm n).
    apply lt_S_n ; auto with arith.
    assumption.
  Defined.

  Implicit Arguments nth [n].
  Require Import Omega.

  Definition vapp : forall n m, vec n -> vec m -> vec (n + m).
  Proof.
    intros.
    induction H.
    simpl.
    assumption.
    
    pose (@vcons (n + m) a IHvec).
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
    vapp _ _ vnil v = v.
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Lemma vapp_vnil_dep_l : forall n, forall v : vec n,
    eq_dep nat vec n (vapp _ _ vnil v) n v.
  Proof.
    intros.
    simpl.
    apply eq_dep_intro.
  Qed.
  
  Lemma vapp_vnil_dep_r : forall n, forall v : vec n,
    eq_dep nat vec (n + 0) (vapp _ _ v vnil) n v.
  Proof.
    intros.
    induction v.
    simpl ; auto.

    simpl.

    pose (proj2 (equiv_eqex_eqdep nat vec (n + 0) n (vapp _ _ v vnil) v) IHv).
    dependent rewrite -> e.
    simpl.
    auto.
  Qed.

  Axiom proof_irrelevance : forall P : Prop, forall p q : P, p = q.

  Lemma cons_nth : forall n i, forall v : vec n, forall a : A, forall p : i < n,
  nth i p v = nth (S i) (lt_n_S _ _ p) (vcons n a v).
  Proof.
  intros i.
  induction i.
  intros.
  elim (lt_n_O _ p).

  intros.
  simpl.
  simpl.
  cut(p = lt_S_n i0 (S i) (lt_n_S i0 (S i) p)).
  intros H ; pattern p at 1 ; rewrite H.
  reflexivity.
  apply proof_irrelevance.
Qed. 

Infix ":::" := vcons (at level 60, right associativity) : vector_scope.
Infix "+++" := vapp (right associativity, at level 60) : vector_scope.

  Implicit Arguments nth [].
  Implicit Arguments vapp [].

Lemma nth_proof_irrel : forall i n, forall l : vec n,
forall p p' : i < n, nth i n p l = nth i n p' l.
Proof.
  intros.
  rewrite (proof_irrelevance (i < n) p p').
  reflexivity.
Qed.

Lemma nth_app : forall i n, forall p : S i < S n, forall l : vec n, forall m, forall l' : vec m, 
  forall x, forall p' : (m + S i) < (m + S n),
  nth (S i) (S n) p (vcons n x l) = 
  nth (m + S i) (m + S n) p' (vapp m (S n) l'  (vcons n x l)).
Proof.
  intros.
  simpl.
  induction l' ; simpl ; intros.
  auto.
  apply nth_proof_irrel.
  simpl.
  apply IHl'.
Qed.

End Vector.

Definition vmap : forall n, forall A B : Set, (A ->  B) -> vec A n -> vec B n.
Proof.
  intros.
  induction H0.
  exact (vnil B).

  exact (vcons _ _ (H a) IHvec).
Defined.

Implicit Arguments nth [A].
Implicit Arguments vcons [A n].
Implicit Arguments vnil [A].



(* 
 Local Variables:
 coq-prog-name: "coqtop.opt -emacs -R . CCP"
 End:
*)
