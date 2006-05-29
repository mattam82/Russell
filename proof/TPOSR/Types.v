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

Reserved Notation "G |-- T -> U : s" (at level 70, T, U, s at next level).

Definition sum_sort s1 s2 s3 :=
  (s1 = set /\ s2 = set /\ s3 = set) \/
  (s1 = prop /\ s2 = prop /\ s3 = prop).

Reserved Notation "G |-- T ~= U : s" (at level 70, T, U, s at next level).

Inductive tposr_wf : lenv -> Prop :=
  | wf_nil : tposr_wf nil
  | wf_cons : forall G A A' s, G |-- A -> A' : Srt_l s -> tposr_wf (A :: G)

with tposr : lenv -> lterm -> lterm -> lterm -> Prop :=
  | tposr_var : forall e, tposr_wf e -> 
  forall n T, item_llift T e n -> e |-- (Ref_l n) -> (Ref_l n) : T

  | tposr_set : forall e, tposr_wf e -> e |-- (Srt_l set) -> (Srt_l set) : Srt_l kind
  | tposr_prop : forall e, tposr_wf e -> e |-- (Srt_l prop) -> (Srt_l prop) : Srt_l kind

  | tposr_prod : forall e A A' s1, e |-- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  e |-- Prod_l A B -> Prod_l A' B' : Srt_l s2
  
  | tposr_abs : forall e A A' s1, e |-- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall M M', (A :: e) |-- M -> M' : B -> 
  e |-- Abs_l A M -> Abs_l A' M' : (Prod_l A B)
  
  | tposr_app : forall e A A' s1, e |-- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall M M', e |-- M -> M' : (Prod_l A B) -> 
  forall N N', e |-- N -> N' : A ->
  e |-- App_l B M N -> App_l B' M' N' : lsubst N B

  | tposr_beta : forall e A A' s1, e |-- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall M M', (A :: e) |-- M -> M' : B -> 
  forall N N', e |-- N -> N' : A ->
  e |-- App_l B (Abs_l A M) N -> lsubst N' M' : lsubst N B

  | tposr_red : forall e M N A, e |-- M -> N : A -> 
  forall B s, e |-- A -> B : Srt_l s ->
  e |-- M -> N : B
  
  | tposr_exp : forall e M N B, e |-- M -> N : B -> 
  forall A s, e |-- A -> B : Srt_l s ->
  e |-- M -> N : A
  
  | tposr_subset : forall e A A', e |-- A -> A' : Srt_l set ->
  forall B B', (A :: e) |-- B -> B' : Srt_l prop ->
  e |-- Subset_l A B -> Subset_l A' B' : Srt_l set

  | tposr_sum : forall e A A' s1, e |-- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  e |-- Sum_l A B -> Sum_l A' B' : Srt_l s3
  
  | tposr_pair : forall e A A' s1, e |-- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u', e |-- u -> u' : A ->
  forall v v', e |-- v -> v' : lsubst u B ->
  e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B

  | tposr_pi1 : forall e A A' s1, e |-- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |-- t -> t' : Sum_l A B ->
  e |-- Pi1_l (Sum_l A B) t -> Pi1_l (Sum_l A' B') t' : A

  | tposr_pi1_red : forall e A A' s1, e |-- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B ->
  forall A'', e |-- A'' ~= A : s1 ->
  forall B'', A'' :: e |-- B'' ~= B : s2 ->
  e |-- Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v) -> u' : A''

  | tposr_pi2 : forall e A A' s1, e |-- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |-- t -> t' : Sum_l A B ->
  e |-- Pi2_l (Sum_l A B) t -> Pi2_l (Sum_l A' B') t' : lsubst (Pi1_l (Sum_l A B) t) B

  | tposr_pi2_red : forall e A A' s1, e |-- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', 
  e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B ->
  e |-- Pi2_l (Sum_l A B) (Pair_l (Sum_l A B) u v) -> v' : lsubst (Pi1_l (Sum_l A B) (Pair_l (Sum_l A B) u v)) B

where "G |-- T -> U : s" := (tposr G T U s)

with tposr_eq : lenv -> lterm -> lterm -> sort -> Prop :=
  | tposr_eq_tposr : forall e X Y s, e |-- X -> Y : Srt_l s -> e |-- X ~= Y : s
  | tposr_eq_sym : forall e X Y s, e |-- X ~= Y : s -> e |-- Y ~= X : s
  | tposr_eq_trans : forall e W X Y s, e |-- W ~= X : s -> e |-- X ~= Y : s ->
  e |-- W ~= Y : s

where "G |-- T ~= U : s" := (tposr_eq G T U s).



Hint Resolve wf_nil tposr_set tposr_prop : coc.

Scheme ind_tposr := Induction for tposr Sort Prop.

Scheme tposr_wf_mutind := Induction for tposr Sort Prop
with wf_tposr_mutind :=  Induction for tposr_wf Sort Prop.

Check tposr_wf_mutind.

Lemma ind_tposr_wf :
forall
         (P : forall (l : lenv) (l0 l1 l2 : lterm),
              l |-- l0 -> l1 : l2 -> Prop)
         (P0 : forall l : lenv, tposr_wf l -> Prop),
       (forall (e : lenv) (t : tposr_wf e),
        P0 e t ->
        forall (n : nat) (T : lterm) (i : item_llift T e n),
        P e (Ref_l n) (Ref_l n) T (tposr_var t i)) ->
       (forall (e : lenv) (t : tposr_wf e),
        P0 e t -> P e (Srt_l set) (Srt_l set) (Srt_l kind) (tposr_set t)) ->
       (forall (e : lenv) (t : tposr_wf e),
        P0 e t -> P e (Srt_l prop) (Srt_l prop) (Srt_l kind) (tposr_prop t)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        P e (Prod_l A B) (Prod_l A' B') (Srt_l s2) (tposr_prod t t0)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (M M' : lterm) (t1 : A :: e |-- M -> M' : B),
        P (A :: e) M M' B t1 ->
        P e (Abs_l A M) (Abs_l A' M') (Prod_l A B) (tposr_abs t t0 t1)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (M M' : lterm) (t1 : e |-- M -> M' : Prod_l A B),
        P e M M' (Prod_l A B) t1 ->
        forall (N N' : lterm) (t2 : e |-- N -> N' : A),
        P e N N' A t2 ->
        P e (App_l B M N) (App_l B' M' N') (lsubst N B)
          (tposr_app t t0 t1 t2)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (M M' : lterm) (t1 : A :: e |-- M -> M' : B),
        P (A :: e) M M' B t1 ->
        forall (N N' : lterm) (t2 : e |-- N -> N' : A),
        P e N N' A t2 ->
        P e (App_l B (Abs_l A M) N) (lsubst N' M') (lsubst N B)
          (tposr_beta t t0 t1 t2)) ->
       (forall (e : lenv) (M N A : lterm) (t : e |-- M -> N : A),
        P e M N A t ->
        forall (B : lterm) (s : sort) (t0 : e |-- A -> B : Srt_l s),
        P e A B (Srt_l s) t0 -> P e M N B (tposr_red t t0)) ->
       (forall (e : lenv) (M N B : lterm) (t : e |-- M -> N : B),
        P e M N B t ->
        forall (A : lterm) (s : sort) (t0 : e |-- A -> B : Srt_l s),
        P e A B (Srt_l s) t0 -> P e M N A (tposr_exp t t0)) ->
       (forall (e : lenv) (A A' : lterm) (t : e |-- A -> A' : Srt_l set),
        P e A A' (Srt_l set) t ->
        forall (B B' : lterm) (t0 : A :: e |-- B -> B' : Srt_l prop),
        P (A :: e) B B' (Srt_l prop) t0 ->
        P e (Subset_l A B) (Subset_l A' B') (Srt_l set) (tposr_subset t t0)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3),
        P e (Sum_l A B) (Sum_l A' B') (Srt_l s3) (tposr_sum t t0 s)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (u u' : lterm)
          (t1 : e |-- u -> u' : A),
        P e u u' A t1 ->
        forall (v v' : lterm) (t2 : e |-- v -> v' : lsubst u B),
        P e v v' (lsubst u B) t2 ->
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          (tposr_pair t t0 s t1 t2)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (t1 t' : lterm)
          (t2 : e |-- t1 -> t' : Sum_l A B),
        P e t1 t' (Sum_l A B) t2 ->
        P e (Pi1_l (Sum_l A B) t1) (Pi1_l (Sum_l A' B') t') A
          (tposr_pi1 t t0 s t2)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (u u' v v' : lterm)
          (t1 : e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v'
                : Sum_l A B),
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          t1 ->
        forall (A'' : lterm) (t2 : e |-- A'' ~= A : s1) (B'' : lterm)
          (t3 : A'' :: e |-- B'' ~= B : s2),
        P e (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) u' A''
          (tposr_pi1_red t t0 s t1 t2 t3)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (t1 t' : lterm)
          (t2 : e |-- t1 -> t' : Sum_l A B),
        P e t1 t' (Sum_l A B) t2 ->
        P e (Pi2_l (Sum_l A B) t1) (Pi2_l (Sum_l A' B') t')
          (lsubst (Pi1_l (Sum_l A B) t1) B) (tposr_pi2 t t0 s t2)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (u u' v v' : lterm)
          (t1 : e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v'
                : Sum_l A B),
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          t1 ->
        P e (Pi2_l (Sum_l A B) (Pair_l (Sum_l A B) u v)) v'
          (lsubst (Pi1_l (Sum_l A B) (Pair_l (Sum_l A B) u v)) B)
          (tposr_pi2_red t t0 s t1)) ->
       P0 nil wf_nil ->
       (forall (G : lenv) (A A' : lterm) (s : sort)
          (t : G |-- A -> A' : Srt_l s),
        P G A A' (Srt_l s) t -> P0 (A :: G) (wf_cons t)) ->
       (forall (l : lenv) (l0 l1 l2 : lterm) (t : l |-- l0 -> l1 : l2),
       P l l0 l1 l2 t) /\
       (forall (l : lenv) (t : tposr_wf l), P0 l t).
Proof.
  intros.
  split.
  intros.
  eapply tposr_wf_mutind with (P := P) (P0 := P0) ; auto ; auto.
  intros.
  eapply wf_tposr_mutind with (P := P) (P0 := P0) ; auto ; auto.
Qed.

Scheme tposr_wf_eq_mutind := Induction for tposr Sort Prop
with wf_tposr_eq_mutind :=  Induction for tposr_wf Sort Prop
with eq_tposr_wf_mutind :=  Induction for tposr_eq Sort Prop.

Check tposr_wf_eq_mutind.

Lemma ind_tposr_wf_eq :
forall
         (P : forall (l : lenv) (l0 l1 l2 : lterm),
              l |-- l0 -> l1 : l2 -> Prop)
         (P0 : forall l : lenv, tposr_wf l -> Prop)
         (P1 : forall (l : lenv) (l0 l1 : lterm) (s : sort),
               l |-- l0 ~= l1 : s -> Prop),
       (forall (e : lenv) (t : tposr_wf e),
        P0 e t ->
        forall (n : nat) (T : lterm) (i : item_llift T e n),
        P e (Ref_l n) (Ref_l n) T (tposr_var t i)) ->
       (forall (e : lenv) (t : tposr_wf e),
        P0 e t -> P e (Srt_l set) (Srt_l set) (Srt_l kind) (tposr_set t)) ->
       (forall (e : lenv) (t : tposr_wf e),
        P0 e t -> P e (Srt_l prop) (Srt_l prop) (Srt_l kind) (tposr_prop t)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        P e (Prod_l A B) (Prod_l A' B') (Srt_l s2) (tposr_prod t t0)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (M M' : lterm) (t1 : A :: e |-- M -> M' : B),
        P (A :: e) M M' B t1 ->
        P e (Abs_l A M) (Abs_l A' M') (Prod_l A B) (tposr_abs t t0 t1)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (M M' : lterm) (t1 : e |-- M -> M' : Prod_l A B),
        P e M M' (Prod_l A B) t1 ->
        forall (N N' : lterm) (t2 : e |-- N -> N' : A),
        P e N N' A t2 ->
        P e (App_l B M N) (App_l B' M' N') (lsubst N B)
          (tposr_app t t0 t1 t2)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (M M' : lterm) (t1 : A :: e |-- M -> M' : B),
        P (A :: e) M M' B t1 ->
        forall (N N' : lterm) (t2 : e |-- N -> N' : A),
        P e N N' A t2 ->
        P e (App_l B (Abs_l A M) N) (lsubst N' M') (lsubst N B)
          (tposr_beta t t0 t1 t2)) ->
       (forall (e : lenv) (M N A : lterm) (t : e |-- M -> N : A),
        P e M N A t ->
        forall (B : lterm) (s : sort) (t0 : e |-- A -> B : Srt_l s),
        P e A B (Srt_l s) t0 -> P e M N B (tposr_red t t0)) ->
       (forall (e : lenv) (M N B : lterm) (t : e |-- M -> N : B),
        P e M N B t ->
        forall (A : lterm) (s : sort) (t0 : e |-- A -> B : Srt_l s),
        P e A B (Srt_l s) t0 -> P e M N A (tposr_exp t t0)) ->
       (forall (e : lenv) (A A' : lterm) (t : e |-- A -> A' : Srt_l set),
        P e A A' (Srt_l set) t ->
        forall (B B' : lterm) (t0 : A :: e |-- B -> B' : Srt_l prop),
        P (A :: e) B B' (Srt_l prop) t0 ->
        P e (Subset_l A B) (Subset_l A' B') (Srt_l set) (tposr_subset t t0)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3),
        P e (Sum_l A B) (Sum_l A' B') (Srt_l s3) (tposr_sum t t0 s)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (u u' : lterm)
          (t1 : e |-- u -> u' : A),
        P e u u' A t1 ->
        forall (v v' : lterm) (t2 : e |-- v -> v' : lsubst u B),
        P e v v' (lsubst u B) t2 ->
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          (tposr_pair t t0 s t1 t2)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (t1 t' : lterm)
          (t2 : e |-- t1 -> t' : Sum_l A B),
        P e t1 t' (Sum_l A B) t2 ->
        P e (Pi1_l (Sum_l A B) t1) (Pi1_l (Sum_l A' B') t') A
          (tposr_pi1 t t0 s t2)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (u u' v v' : lterm)
          (t1 : e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v'
                : Sum_l A B),
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          t1 ->
        forall (A'' : lterm) (t2 : e |-- A'' ~= A : s1),
        P1 e A'' A s1 t2 ->
        forall (B'' : lterm) (t3 : A'' :: e |-- B'' ~= B : s2),
        P1 (A'' :: e) B'' B s2 t3 ->
        P e (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) u' A''
          (tposr_pi1_red t t0 s t1 t2 t3)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (t1 t' : lterm)
          (t2 : e |-- t1 -> t' : Sum_l A B),
        P e t1 t' (Sum_l A B) t2 ->
        P e (Pi2_l (Sum_l A B) t1) (Pi2_l (Sum_l A' B') t')
          (lsubst (Pi1_l (Sum_l A B) t1) B) (tposr_pi2 t t0 s t2)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort)
          (t : e |-- A -> A' : Srt_l s1),
        P e A A' (Srt_l s1) t ->
        forall (B B' : lterm) (s2 : sort)
          (t0 : A :: e |-- B -> B' : Srt_l s2),
        P (A :: e) B B' (Srt_l s2) t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (u u' v v' : lterm)
          (t1 : e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v'
                : Sum_l A B),
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          t1 ->
        P e (Pi2_l (Sum_l A B) (Pair_l (Sum_l A B) u v)) v'
          (lsubst (Pi1_l (Sum_l A B) (Pair_l (Sum_l A B) u v)) B)
          (tposr_pi2_red t t0 s t1)) ->
       P0 nil wf_nil ->
       (forall (G : lenv) (A A' : lterm) (s : sort)
          (t : G |-- A -> A' : Srt_l s),
        P G A A' (Srt_l s) t -> P0 (A :: G) (wf_cons t)) ->
       (forall (e : lenv) (X Y : lterm) (s : sort)
          (t : e |-- X -> Y : Srt_l s),
        P e X Y (Srt_l s) t -> P1 e X Y s (tposr_eq_tposr t)) ->
       (forall (e : lenv) (X Y : lterm) (s : sort) (t : e |-- X ~= Y : s),
        P1 e X Y s t -> P1 e Y X s (tposr_eq_sym t)) ->
       (forall (e : lenv) (W X Y : lterm) (s : sort) (t : e |-- W ~= X : s),
        P1 e W X s t ->
        forall t0 : e |-- X ~= Y : s,
        P1 e X Y s t0 -> P1 e W Y s (tposr_eq_trans t t0)) ->

       (forall (l : lenv) (l0 l1 l2 : lterm) (t : l |-- l0 -> l1 : l2),
       P l l0 l1 l2 t) /\
       (forall (l : lenv) (t : tposr_wf l), P0 l t) /\
       (forall (l : lenv) (l0 l1 : lterm) (s : sort) (t : l |-- l0 ~= l1 : s),
       P1 l l0 l1 s t).
Proof.
  intros.
  split.
  intros.
  eapply tposr_wf_eq_mutind with (P := P) (P0 := P0) (P1 := P1); auto ; auto.
  split ;intros.
  eapply wf_tposr_eq_mutind with (P := P) (P0 := P0) (P1 := P1) ; auto ; auto.
  eapply eq_tposr_wf_mutind with (P := P) (P0 := P0) (P1 := P1) ; auto ; auto.
Qed.

Definition tposr_term G M A := exists M', G |-- M -> M' : A.

Inductive tposrp : lenv -> lterm -> lterm -> lterm -> Prop :=
  | tposrp_tposr : forall e X Y Z, e |-- X -> Y : Z -> tposrp e X Y Z
  | tposrp_trans : forall e W X Y Z, tposrp e W X Z -> tposrp e X Y Z ->
  tposrp e W Y Z.

Hint Resolve tposr_eq_tposr tposr_eq_sym tposrp_tposr : coc.