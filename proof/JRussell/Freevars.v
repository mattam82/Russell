Require Import Lambda.Terms.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Env.
Require Import JRussell.Types.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Lemma free_db_lift1_rec : forall n t, free_db n t -> forall k, free_db (S n) (lift_rec 1 t k).
Proof.
  simple induction 1 ; simpl ; intros ; auto with coc core arith datatypes.

  elim (le_gt_dec k0 n0) ; simpl ; intros ;
  constructor ; auto with arith.
Qed.

Lemma free_db_lift1 : forall n t, free_db n t -> free_db (S n) (lift 1 t).
Proof.
  unfold lift ; intros ; apply free_db_lift1_rec ; assumption.
Qed.

Hint Resolve free_db_lift1 : coc.

Lemma free_db_lift_rec : forall n t, free_db n t -> forall n' k, free_db (n' + n) (lift_rec n' t k).
Proof.
  assert(forall n' k, S (n' + k) = n' + S k) ; try (intros ; omega). 
  simple induction 1 ; simpl ; intros ; try constructor ; try rewrite H ; auto with coc core arith datatypes.

  elim (le_gt_dec k0 n0) ; simpl ; intros ;
  constructor ; auto with arith.
  omega.
Qed.

Require Import Omega.
Require Import Arith.

Lemma term_free_db : forall e t T, e |- t : T -> free_db (length e) t.
Proof.
  simple induction 1 ; intros ; auto with coc core arith datatypes.

  simpl.
  constructor.
  auto with arith.

  simpl ; apply free_db_lift1.
  assumption.
Qed.

Hint Resolve term_free_db : coc.

  Lemma free_db_subst_rec : forall t n, free_db (S n) t -> 
    forall m t', free_db m t' -> n >= m -> free_db n (subst_rec t' t (n - m)).
Proof.

  assert(Hsnk : forall n k, S (n + k) = n + S k) ; try (intros ; omega). 
  induction t ; simpl ; intros ; try inversion H ; try constructor ; try rewrite Hsnk ; auto with coc core arith datatypes.
  
  elim (lt_eq_lt_dec (n0 - m) n) ; simpl ; intros ; 
  auto with arith.
  destruct a.
  constructor ; auto with arith.
  inversion H.
  omega.
  unfold lift.
  pose (free_db_lift_rec).
  rewrite e.
   pose (f m t' H0 n).
  assert(n0 = n + m) ; try omega.
  rewrite H5.
  apply f0.
  
  constructor.
  omega.
  
  assert(S (n - m) = (S n) - m) ; try omega.
  rewrite H7.
  apply IHt2 ; auto.

  assert(S (n - m) = (S n) - m) ; try omega.
  rewrite H7.
  apply IHt2 ; auto.

  assert(S (n - m) = (S n) - m) ; try omega.
  rewrite H7.
  apply IHt2 ; auto.

  assert(S (n - m) = (S n) - m) ; try omega.
  rewrite H7.
  apply IHt2 ; auto.
Qed.


Lemma free_db_subst : forall t n, free_db (S n) t -> 
 forall t', free_db n t'-> free_db n (subst t' t).
Proof.
  unfold subst ; intros.
  assert(n - n = 0) ; try omega.
  rewrite <- H1.
  apply free_db_subst_rec ; auto with arith.
Qed.

Lemma type_free_db : 
  (forall e t T, e |- t : T -> free_db (length e) T) /\
  (forall e U V s, e |- U >> V : s -> free_db (length e) U /\ free_db (length e) V) /\
  (forall e U V T, e |- U = V : T -> free_db (length e) U /\ free_db (length e) V).
Proof.
  apply typ_coerce_jeq_ind with
  (P:= fun e t T => fun H : e |- t : T => free_db (length e) T)
  (P0:= fun e U V s => fun H : e |- U >> V : s => free_db (length e) U /\ free_db (length e) V)
  (P1 := fun e U V T => fun H : e |- U = V : T => free_db (length e) U /\ free_db (length e) V) ;
  simpl ; intros ; intuition ; try constructor ; try (apply (term_free_db t)) ; auto with coc core arith datatypes.

  apply free_db_lift1 ;  apply term_free_db with (Srt s) ; auto.

  inversion H0.
  pose (term_free_db t).
  apply free_db_subst ; auto.
  
  apply (term_free_db t1).

  inversion H.
  assumption.
  
  inversion H.
  pose (term_free_db t0).
  assert(free_db (length e) (Pi1 t)).
  constructor ; auto.
  apply free_db_subst ; auto.


  apply (term_free_db t1).

  apply (term_free_db t1).

  constructor ; auto.
  apply (term_free_db t1).
  apply (term_free_db t2).
  
  apply free_db_subst ; auto.
  apply (term_free_db t1).
  apply (term_free_db t2).

  constructor ; auto.
  constructor ; auto.
  apply (term_free_db t0).
  apply (term_free_db t1).
  apply (term_free_db t2).
  apply (term_free_db t1).
  
  constructor ; auto.
  constructor ; auto.
  apply (term_free_db t0).
  apply (term_free_db t1).
  apply (term_free_db t2).
  apply (term_free_db t2).
Qed.

Lemma typ_free_db : forall e t T, e |- t : T -> free_db (length e) T.
Proof (proj1 (type_free_db)).

Lemma coerce_free_db : forall e T U s, e |- T >> U : s -> free_db (length e) T /\ free_db (length e) U.
Proof (proj1 (proj2 (type_free_db))).

Lemma jeq_free_db : forall e U V T , e |- U = V : T -> free_db (length e) U /\ free_db (length e) V.
Proof (proj2 (proj2 (type_free_db))).
