Require Import Lambda.Tactics.
Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.

Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Thinning.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.RightReflexivity.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Require Export Coq.Arith.Max.

Reserved Notation "G |-- T >-> U : s [ n ]" (at level 70, T, U, s at next level).
 
Inductive coerce_rc_depth : lenv -> lterm -> lterm -> sort -> nat -> Prop :=
  | coerce_rc_depth_refl : forall e A s, e |-- A -> A : s -> e |-- A >-> A : s [0]

  | coerce_rc_depth_prod : forall e A B A' B',
  forall s n, e |-- A' >-> A : s [n] ->
  (* derivable *) e |-- A' -> A' : s -> e |-- A -> A : s ->
  forall s' m, (A' :: e) |-- B >-> B' : s' [m] ->
  (* derivable *) A :: e |-- B -> B : s' -> A' :: e |-- B' -> B' : s' ->
  e |-- (Prod_l A B) >-> (Prod_l A' B') : s' [S (max n m)]

  | coerce_rc_depth_sum : forall e A B A' B',
  forall s n, e |-- A >-> A' : s [n] ->
  (* derivable *) e |-- A' -> A' : s -> e |-- A -> A : s ->
  forall s' m, (A :: e) |-- B >-> B' : s' [m] ->
  (* derivable *) A :: e |-- B -> B : s' -> A' :: e |-- B' -> B' : s' ->
  forall s'', sum_sort s s' s'' ->
  e |-- (Sum_l A B) >-> (Sum_l A' B') : s'' [S (max n m)]

  | coerce_rc_depth_sub_l : forall e U P U' n,
  e |-- U >-> U' : set [n] ->
  (* derivable *) U :: e |-- P -> P : prop ->
  e |-- Subset_l U P >-> U' : set [S n]

  | coerce_rc_depth_sub_r : forall e U U' P n,
  e |-- U >-> U' : set [n] ->
  (* derivable *) U' :: e |-- P -> P : prop ->
  e |-- U >-> (Subset_l U' P) : set [S n]

  | coerce_rc_depth_conv_l : forall e A B C s n,
  e |-- A -> A : s -> e |-- B -> B : s -> e |-- C -> C : s ->
  e |-- A ~= B : s -> e |-- B >-> C : s [n] -> e |-- A >-> C : s [S n]

 | coerce_rc_depth_conv_r : forall e A B C s n,
  e |-- A -> A : s -> e |-- B -> B : s -> e |-- C -> C : s ->
  e |-- A >-> B : s [n] -> e |-- B ~= C : s -> e |-- A >-> C : s [S n]

where "G |-- T >-> U : s [ n ] " := (coerce_rc_depth G T U s n).

Hint Resolve coerce_rc_depth_refl coerce_rc_depth_prod coerce_rc_depth_sum coerce_rc_depth_sub_l coerce_rc_depth_sub_r : coc.
Hint Resolve coerce_rc_depth_conv_l coerce_rc_depth_conv_r : coc.

Scheme coerce_rc_depth_dep := Induction for coerce_rc_depth Sort Prop.

Lemma coerce_rc_depth_coerce : forall G T U s n, G |-- T >-> U : s [n] -> G |-- T >-> U : s.
Proof.
  induction 1 ; intros ; auto with coc core ; eauto with ecoc.

  apply tposr_coerce_sub_l ; auto with coc.
  apply (coerce_refl_l IHcoerce_rc_depth).
  apply (coerce_refl_r IHcoerce_rc_depth).
  
  apply tposr_coerce_sub_r ; auto with coc.
  apply (coerce_refl_l IHcoerce_rc_depth).
  apply (coerce_refl_r IHcoerce_rc_depth).
  
  apply tposr_coerce_trans with B ; auto with coc.
  apply tposr_coerce_trans with B ; auto with coc.
Qed.
