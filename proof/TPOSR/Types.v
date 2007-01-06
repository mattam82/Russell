Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.

Set Implicit Arguments.
Implicit Types s : sort.

(** printing |-- $\type$ *)
(** printing -> $"->"$ *)

Reserved Notation "G |-- T -> U : s" (at level 70, T, U, s at next level).

Definition sum_sort s1 s2 s3 :=
  (s1 = set /\ s2 = set /\ s3 = set) \/
  (s1 = prop /\ s2 = prop /\ s3 = prop).

Coercion Srt_l : sort >-> lterm.
(** printing ~= $\simeq$ *)
(** printing >-> $\sub$ *)
Reserved Notation "G |-- T ~= U : s" (at level 70, T, U, s at next level).
Reserved Notation "G |-- T >-> U : s" (at level 70, T, U, s at next level).

Inductive tposr_wf : lenv -> Prop :=
  | wf_nil : tposr_wf nil
  | wf_cons : forall G A s, G |-- A -> A : s -> tposr_wf (A :: G)


with tposr : lenv -> lterm -> lterm -> lterm -> Prop :=

  | tposr_var : forall e, tposr_wf e -> 
  forall n T, item_llift T e n -> e |-- (Ref_l n) -> (Ref_l n) : T

  | tposr_set : forall e, tposr_wf e -> e |-- set -> set : kind

  | tposr_prop : forall e, tposr_wf e -> e |-- prop -> prop : kind

  | tposr_prod : forall e A A' s1, e |-- A -> A' : s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : s2 ->
  e |-- Prod_l A B -> Prod_l A' B' : s2
  
  | tposr_abs : forall e A A' s1, e |-- A -> A' : s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : s2 ->
  forall M M', (A :: e) |-- M -> M' : B -> 
  e |-- Abs_l A M -> Abs_l A' M' : (Prod_l A B)
  
  | tposr_app : forall e A A' s1, e |-- A -> A' : s1 ->
  forall B B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall M M', e |-- M -> M' : (Prod_l A B) -> 
  forall N N', e |-- N -> N' : A ->
  e |-- App_l B M N -> App_l B' M' N' : lsubst N B

  | tposr_beta : forall e A A' s1, e |-- A -> A' : s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : s2 ->
  forall M M', (A :: e) |-- M -> M' : B -> 
  forall N N', e |-- N -> N' : A ->
  e |-- App_l B (Abs_l A M) N -> lsubst N' M' : lsubst N B

  | tposr_conv : forall e M N A, e |-- M -> N : A -> 
  forall B s, e |-- A >-> B : s ->
  e |-- M -> N : B
  
  | tposr_subset : forall e A A', e |-- A -> A' : set ->
  forall B B', (A :: e) |-- B -> B' : prop ->
  e |-- Subset_l A B -> Subset_l A' B' : set

  | tposr_sum : forall e A A' s1, e |-- A -> A' : s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  e |-- Sum_l A B -> Sum_l A' B' : s3
  
  | tposr_pair : forall e A A' s1, e |-- A -> A' : s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u', e |-- u -> u' : A ->
  forall v v', e |-- v -> v' : lsubst u B ->
  e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B

  | tposr_pi1 : forall e A A' s1, e |-- A -> A : s1 -> e |-- A >-> A' : s1 ->
  forall B B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |-- t -> t' : Sum_l A B ->
  e |-- Pi1_l (Sum_l A B) t -> Pi1_l (Sum_l A' B') t' : A

  | tposr_pi1_red : forall e A A' s1, e |-- A -> A' : s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B ->
  forall A'', e |-- A'' -> A'' : s1 -> e |-- A'' >-> A : s1 ->
  forall B'', A'' :: e |-- B'' >-> B : s2 ->
  e |-- Sum_l A'' B'' >-> Sum_l A B : s3 ->
  e |-- Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v) -> u' : A''

  | tposr_pi2 : forall e A A' s1, e |-- A -> A : s1 -> e |-- A >-> A' : s1 ->
  forall B B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |-- t -> t' : Sum_l A B ->
  e |-- Pi2_l (Sum_l A B) t -> Pi2_l (Sum_l A' B') t' : lsubst (Pi1_l (Sum_l A B) t) B

 | tposr_pi2_red : forall e A A' s1, e |-- A -> A' : s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', 
  e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B ->
  forall A'', e |-- A'' -> A'' : s1 -> e |-- A'' >-> A : s1 ->
  forall B'', A'' :: e |-- B'' >-> B : s2 ->
  e |-- Sum_l A'' B'' >-> Sum_l A B : s3 ->
  e |-- Pi2_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v) -> v' : lsubst (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) B''

where "G |-- T -> U : s" := (tposr G T U s)

with tposr_eq : lenv -> lterm -> lterm -> sort -> Prop :=
  | tposr_eq_tposr : forall e X Y s, e |-- X -> Y : s -> e |-- X ~= Y : s
  | tposr_eq_sym : forall e X Y s, e |-- X ~= Y : s -> e |-- Y ~= X : s
  | tposr_eq_trans : forall e W X Y s, e |-- W ~= X : s -> e |-- X ~= Y : s -> e |-- W ~= Y : s

where "G |-- T ~= U : s" := (tposr_eq G T U s)

with tposr_coerce : lenv -> lterm -> lterm -> sort -> Prop :=
  | tposr_coerce_conv : forall e A B s,  e |-- A ~= B : s -> e |-- A >-> B : s
  
  | tposr_coerce_prod : forall e A B A' B',
  forall s, e |-- A' >-> A : s ->
  (* derivable *) e |-- A' -> A' :  s -> e |-- A -> A :  s ->
  forall s', (A' :: e) |-- B >-> B' : s' -> 
  (* derivable *) A :: e |-- B -> B :  s' -> A' :: e |-- B' -> B' :  s' ->
  e |-- (Prod_l A B) >-> (Prod_l A' B') : s'
  
  | tposr_coerce_sum : forall e A B A' B',
  forall s, e |-- A >-> A' : s -> 
  (* derivable *) e |-- A' -> A' :  s -> e |-- A -> A :  s ->
  forall s', (A :: e) |-- B >-> B' : s' ->
  (* derivable *) A :: e |-- B -> B :  s' -> A' :: e |-- B' -> B' :  s' ->
  forall s'', sum_sort s s' s'' -> 
  e |-- (Sum_l A B) >-> (Sum_l A' B') : s''

  | tposr_coerce_sub_l : forall e U P U', 	
  e |-- U >-> U' : set ->
  (* derivable *) e |-- U -> U :  set -> e |-- U' -> U' :  set -> 
  (* derivable *) U :: e |-- P -> P :  prop ->
  e |-- Subset_l U P >-> U' : set

  | tposr_coerce_sub_r : forall e U U' P,
  e |-- U >-> U' : set -> 
  (* derivable *) e |-- U -> U :  set -> e |-- U' -> U' :  set ->
  (* derivable *) U' :: e |-- P -> P : prop ->
  e |-- U >-> (Subset_l U' P) : set

  | tposr_coerce_sym : forall e U V s, e |-- U >-> V : s -> e |-- V >-> U : s

  | tposr_coerce_trans : forall e A B C s,  
  e |-- A >-> B : s -> e |-- B >-> C : s -> e |-- A >-> C : s

where "G |-- T >-> U : s" := (tposr_coerce G T U s).

(* begin hide *)
Hint Resolve wf_nil tposr_set tposr_prop : coc.
Hint Resolve tposr_pi2_red tposr_pi2 tposr_pi1_red tposr_pi1 tposr_pair tposr_sum tposr_subset tposr_conv : coc.
Hint Resolve tposr_beta tposr_app tposr_var tposr_prod tposr_app : coc.
Hint Resolve wf_cons : ecoc.

Hint Resolve tposr_eq_tposr tposr_eq_sym : coc.
Hint Resolve tposr_eq_trans : ecoc.

Hint Resolve tposr_coerce_conv tposr_coerce_sym tposr_coerce_sub_l tposr_coerce_sub_r : coc.
Hint Resolve tposr_coerce_prod tposr_coerce_sum tposr_coerce_trans : ecoc.

(* end hide *)

Scheme ind_tposr := Induction for tposr Sort Prop.

Scheme tposr_wf_mutind := Induction for tposr Sort Prop
with wf_tposr_mutind :=  Induction for tposr_wf Sort Prop.

Combined Scheme ind_tposr_wf from tposr_wf_mutind, wf_tposr_mutind.

Scheme tposr_mutind := Induction for tposr Sort Prop
with wf_mutind :=  Induction for tposr_wf Sort Prop
with eq_mutind :=  Induction for tposr_eq Sort Prop
with coerce_mutind :=  Induction for tposr_coerce Sort Prop.

Combined Scheme ind_tposr_wf_eq_coerce from tposr_mutind, wf_mutind, eq_mutind, coerce_mutind.

Lemma wf_tposr : forall e M N T, e |-- M -> N : T -> tposr_wf e.
Proof.
  induction 1 ; simpl ; auto with coc.
Qed.

Hint Resolve wf_tposr : ecoc.
(** printing -+> $"->"^+$ *)
Reserved Notation "G |-- M -+> N : B" (at level 70, M, N, B at next level). 

Inductive tposrp : lenv -> lterm -> lterm -> lterm -> Prop :=
  | tposrp_tposr : forall e X Y Z, e |-- X -> Y : Z -> e |-- X -+> Y : Z
  | tposrp_trans : forall e W X Y Z, e |-- W -+> X : Z -> e |-- X -+> Y : Z -> e |-- W -+> Y : Z
where "G |-- M -+> N : B" := (tposrp G M N B). 

Hint Resolve tposrp_tposr : coc.
Hint Resolve tposrp_trans : ecoc.

Definition tposr_term G M A := exists M', G |-- M -> M' : A.

Lemma tposr_tposr_term : forall G M M' A, tposr G M M' A -> tposr_term G M A.
Proof.
intros ; exists M' ; auto.
Qed.

Hint Resolve tposr_tposr_term : ecoc.
