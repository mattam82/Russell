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

Coercion Srt_l : sort >-> lterm.

Implicit Types s : sort.

Reserved Notation "G |-- T ~= U : s" (at level 70, T, U, s at next level).
Reserved Notation "G |-- T >-> U : s" (at level 70, T, U, s at next level).

Inductive tposr_wf : lenv -> Prop :=
  | wf_nil : tposr_wf nil
  | wf_cons : forall G A A' s, G |-- A -> A' : s -> tposr_wf (A :: G)

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

  | tposr_pi1 : forall e A A' s1, e |-- A >-> A' : s1 ->
  forall B B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |-- t -> t' : Sum_l A B ->
  e |-- Pi1_l (Sum_l A B) t -> Pi1_l (Sum_l A' B') t' : A

  | tposr_pi1_red : forall e A A' s1, e |-- A -> A' : s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B ->
  forall A'', e |-- A'' >-> A : s1 ->
  forall B'', A'' :: e |-- B'' >-> B : s2 ->
  e |-- Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v) -> u' : A''

  | tposr_pi2 : forall e A A' s1, e |-- A >-> A' : s1 ->
  forall B B' s2, (A :: e) |-- B >-> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |-- t -> t' : Sum_l A B ->
  e |-- Pi2_l (Sum_l A B) t -> Pi2_l (Sum_l A' B') t' : lsubst (Pi1_l (Sum_l A B) t) B

  | tposr_pi2_red : forall e A A' s1, e |-- A -> A' : s1 ->
  forall B B' s2, (A :: e) |-- B -> B' : s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', 
  e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B ->
  forall A'', e |-- A'' >-> A : s1 ->
  forall B'', A'' :: e |-- B'' >-> B : s2 ->
  e |-- Pi2_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v) -> v' : lsubst (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) B''

where "G |-- T -> U : s" := (tposr G T U s)

with tposr_eq : lenv -> lterm -> lterm -> sort -> Prop :=
  | tposr_eq_tposr : forall e X Y s, e |-- X -> Y : s -> e |-- X ~= Y : s
  | tposr_eq_sym : forall e X Y s, e |-- X ~= Y : s -> e |-- Y ~= X : s
  | tposr_eq_trans : forall e W X Y s, e |-- W ~= X : s -> e |-- X ~= Y : s ->
  e |-- W ~= Y : s

where "G |-- T ~= U : s" := (tposr_eq G T U s)

with tposr_coerce : lenv -> lterm -> lterm -> sort -> Prop :=
  | tposr_coerce_conv : forall e A B s,  e |-- A -> A : s -> e |-- B -> B : s -> e |-- A ~= B : s -> e |-- A >-> B : s
  
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
  forall s'', sum_sort s s' s'' -> sum_sort s s' s'' ->
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

Hint Resolve wf_nil tposr_set tposr_prop : coc.
Hint Resolve tposr_pi2_red tposr_pi2 tposr_pi1_red tposr_pi1 tposr_pair tposr_sum tposr_subset tposr_conv : coc.
Hint Resolve tposr_beta tposr_app tposr_var tposr_prod tposr_app : coc.

Hint Resolve tposr_eq_tposr tposr_eq_sym : coc.
Hint Resolve tposr_eq_trans : ecoc.

Hint Resolve tposr_coerce_conv tposr_coerce_sym tposr_coerce_sub_l tposr_coerce_sub_r : coc.
Hint Resolve tposr_coerce_prod tposr_coerce_sum tposr_coerce_trans : ecoc.

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
        P0 e t -> P e set set kind (tposr_set t)) ->
       (forall (e : lenv) (t : tposr_wf e),
        P0 e t -> P e prop prop kind (tposr_prop t)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        P e (Prod_l A B) (Prod_l A' B') s2 (tposr_prod t t0)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        forall (M M' : lterm) (t1 : A :: e |-- M -> M' : B),
        P (A :: e) M M' B t1 ->
        P e (Abs_l A M) (Abs_l A' M') (Prod_l A B) (tposr_abs t t0 t1)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B >-> B' : s2)
          (M M' : lterm) (t1 : e |-- M -> M' : Prod_l A B),
        P e M M' (Prod_l A B) t1 ->
        forall (N N' : lterm) (t2 : e |-- N -> N' : A),
        P e N N' A t2 ->
        P e (App_l B M N) (App_l B' M' N') (lsubst N B)
          (tposr_app t t0 t1 t2)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        forall (M M' : lterm) (t1 : A :: e |-- M -> M' : B),
        P (A :: e) M M' B t1 ->
        forall (N N' : lterm) (t2 : e |-- N -> N' : A),
        P e N N' A t2 ->
        P e (App_l B (Abs_l A M) N) (lsubst N' M') (lsubst N B)
          (tposr_beta t t0 t1 t2)) ->
       (forall (e : lenv) (M N A : lterm) (t : e |-- M -> N : A),
        P e M N A t ->
        forall (B : lterm) s (t0 : e |-- A >-> B : s),
        P e M N B (tposr_conv t t0)) ->
       (forall (e : lenv) (A A' : lterm) (t : e |-- A -> A' : set),
        P e A A' set t ->
        forall (B B' : lterm) (t0 : A :: e |-- B -> B' : prop),
        P (A :: e) B B' prop t0 ->
        P e (Subset_l A B) (Subset_l A' B') set (tposr_subset t t0)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        forall s3 (s : sum_sort s1 s2 s3),
        P e (Sum_l A B) (Sum_l A' B') s3 (tposr_sum t t0 s)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        forall s3 (s : sum_sort s1 s2 s3) (u u' : lterm)
          (t1 : e |-- u -> u' : A),
        P e u u' A t1 ->
        forall (v v' : lterm) (t2 : e |-- v -> v' : lsubst u B),
        P e v v' (lsubst u B) t2 ->
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          (tposr_pair t t0 s t1 t2)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A >-> A' : s1)
          (B B' : lterm) s2 (t0 : A :: e |-- B >-> B' : s2) s3
          (s : sum_sort s1 s2 s3) (t1 t' : lterm)
          (t2 : e |-- t1 -> t' : Sum_l A B),
        P e t1 t' (Sum_l A B) t2 ->
        P e (Pi1_l (Sum_l A B) t1) (Pi1_l (Sum_l A' B') t') A
          (tposr_pi1 t t0 s t2)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        forall s3 (s : sum_sort s1 s2 s3) (u u' v v' : lterm)
          (t1 : e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v'
                : Sum_l A B),
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          t1 ->
        forall (A'' : lterm) (t2 : e |-- A'' >-> A : s1) (B'' : lterm)
          (t3 : A'' :: e |-- B'' >-> B : s2),
        P e (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) u' A''
          (tposr_pi1_red t t0 s t1 t2 t3)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A >-> A' : s1)
          (B B' : lterm) s2 (t0 : A :: e |-- B >-> B' : s2) s3
          (s : sum_sort s1 s2 s3) (t1 t' : lterm)
          (t2 : e |-- t1 -> t' : Sum_l A B),
        P e t1 t' (Sum_l A B) t2 ->
        P e (Pi2_l (Sum_l A B) t1) (Pi2_l (Sum_l A' B') t')
          (lsubst (Pi1_l (Sum_l A B) t1) B) (tposr_pi2 t t0 s t2)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        forall s3 (s : sum_sort s1 s2 s3) (u u' v v' : lterm)
          (t1 : e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v'
                : Sum_l A B),
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          t1 ->
        forall (A'' : lterm) (t2 : e |-- A'' >-> A : s1) (B'' : lterm)
          (t3 : A'' :: e |-- B'' >-> B : s2),
        P e (Pi2_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) v'
          (lsubst (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) B'')
          (tposr_pi2_red t t0 s t1 t2 t3)) ->
       P0 nil wf_nil ->
       (forall (G : lenv) (A A' : lterm) s (t : G |-- A -> A' : s),
        P G A A' s t -> P0 (A :: G) (wf_cons t)) ->

       (forall (G : lenv) (A A' : lterm) s (t : G |-- A -> A' : s),
        P G A A' s t -> P0 (A :: G) (wf_cons t)) ->
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

Scheme tposr_mutind := Induction for tposr Sort Prop
with wf_mutind :=  Induction for tposr_wf Sort Prop
with eq_mutind :=  Induction for tposr_eq Sort Prop
with coerce_mutind :=  Induction for tposr_coerce Sort Prop.

Check tposr_mutind.

Lemma ind_tposr_wf_eq_coerce :
 forall
         (P : forall (l : lenv) (l0 l1 l2 : lterm),
              l |-- l0 -> l1 : l2 -> Prop)
         (P0 : forall l : lenv, tposr_wf l -> Prop)
         (P1 : forall (l : lenv) (l0 l1 : lterm) s,
               l |-- l0 ~= l1 : s -> Prop)
         (P2 : forall (l : lenv) (l0 l1 : lterm) s,
               l |-- l0 >-> l1 : s -> Prop),
       (forall (e : lenv) (t : tposr_wf e),
        P0 e t ->
        forall (n : nat) (T : lterm) (i : item_llift T e n),
        P e (Ref_l n) (Ref_l n) T (tposr_var t i)) ->
       (forall (e : lenv) (t : tposr_wf e),
        P0 e t -> P e set set kind (tposr_set t)) ->
       (forall (e : lenv) (t : tposr_wf e),
        P0 e t -> P e prop prop kind (tposr_prop t)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        P e (Prod_l A B) (Prod_l A' B') s2 (tposr_prod t t0)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        forall (M M' : lterm) (t1 : A :: e |-- M -> M' : B),
        P (A :: e) M M' B t1 ->
        P e (Abs_l A M) (Abs_l A' M') (Prod_l A B) (tposr_abs t t0 t1)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B >-> B' : s2),
        P2 (A :: e) B B' s2 t0 ->
        forall (M M' : lterm) (t1 : e |-- M -> M' : Prod_l A B),
        P e M M' (Prod_l A B) t1 ->
        forall (N N' : lterm) (t2 : e |-- N -> N' : A),
        P e N N' A t2 ->
        P e (App_l B M N) (App_l B' M' N') (lsubst N B)
          (tposr_app t t0 t1 t2)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        forall (M M' : lterm) (t1 : A :: e |-- M -> M' : B),
        P (A :: e) M M' B t1 ->
        forall (N N' : lterm) (t2 : e |-- N -> N' : A),
        P e N N' A t2 ->
        P e (App_l B (Abs_l A M) N) (lsubst N' M') (lsubst N B)
          (tposr_beta t t0 t1 t2)) ->
       (forall (e : lenv) (M N A : lterm) (t : e |-- M -> N : A),
        P e M N A t ->
        forall (B : lterm) s (t0 : e |-- A >-> B : s),
        P2 e A B s t0 -> P e M N B (tposr_conv t t0)) ->
       (forall (e : lenv) (A A' : lterm) (t : e |-- A -> A' : set),
        P e A A' set t ->
        forall (B B' : lterm) (t0 : A :: e |-- B -> B' : prop),
        P (A :: e) B B' prop t0 ->
        P e (Subset_l A B) (Subset_l A' B') set (tposr_subset t t0)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        forall s3 (s : sum_sort s1 s2 s3),
        P e (Sum_l A B) (Sum_l A' B') s3 (tposr_sum t t0 s)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        forall s3 (s : sum_sort s1 s2 s3) (u u' : lterm)
          (t1 : e |-- u -> u' : A),
        P e u u' A t1 ->
        forall (v v' : lterm) (t2 : e |-- v -> v' : lsubst u B),
        P e v v' (lsubst u B) t2 ->
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          (tposr_pair t t0 s t1 t2)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A >-> A' : s1),
        P2 e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B >-> B' : s2),
        P2 (A :: e) B B' s2 t0 ->
        forall s3 (s : sum_sort s1 s2 s3) (t1 t' : lterm)
          (t2 : e |-- t1 -> t' : Sum_l A B),
        P e t1 t' (Sum_l A B) t2 ->
        P e (Pi1_l (Sum_l A B) t1) (Pi1_l (Sum_l A' B') t') A
          (tposr_pi1 t t0 s t2)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        forall s3 (s : sum_sort s1 s2 s3) (u u' v v' : lterm)
          (t1 : e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v'
                : Sum_l A B),
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          t1 ->
        forall (A'' : lterm) (t2 : e |-- A'' >-> A : s1),
        P2 e A'' A s1 t2 ->
        forall (B'' : lterm) (t3 : A'' :: e |-- B'' >-> B : s2),
        P2 (A'' :: e) B'' B s2 t3 ->
        P e (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) u' A''
          (tposr_pi1_red t t0 s t1 t2 t3)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A >-> A' : s1),
        P2 e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B >-> B' : s2),
        P2 (A :: e) B B' s2 t0 ->
        forall s3 (s : sum_sort s1 s2 s3) (t1 t' : lterm)
          (t2 : e |-- t1 -> t' : Sum_l A B),
        P e t1 t' (Sum_l A B) t2 ->
        P e (Pi2_l (Sum_l A B) t1) (Pi2_l (Sum_l A' B') t')
          (lsubst (Pi1_l (Sum_l A B) t1) B) (tposr_pi2 t t0 s t2)) ->
       (forall (e : lenv) (A A' : lterm) s1 (t : e |-- A -> A' : s1),
        P e A A' s1 t ->
        forall (B B' : lterm) s2 (t0 : A :: e |-- B -> B' : s2),
        P (A :: e) B B' s2 t0 ->
        forall s3 (s : sum_sort s1 s2 s3) (u u' v v' : lterm)
          (t1 : e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v'
                : Sum_l A B),
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          t1 ->
        forall (A'' : lterm) (t2 : e |-- A'' >-> A : s1),
        P2 e A'' A s1 t2 ->
        forall (B'' : lterm) (t3 : A'' :: e |-- B'' >-> B : s2),
        P2 (A'' :: e) B'' B s2 t3 ->
        P e (Pi2_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) v'
          (lsubst (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) B'')
          (tposr_pi2_red t t0 s t1 t2 t3)) ->
       P0 nil wf_nil ->
       (forall (G : lenv) (A A' : lterm) s (t : G |-- A -> A' : s),
        P G A A' s t -> P0 (A :: G) (wf_cons t)) ->
       (forall (e : lenv) (X Y : lterm) s (t : e |-- X -> Y : s),
        P e X Y s t -> P1 e X Y s (tposr_eq_tposr t)) ->
       (forall (e : lenv) (X Y : lterm) s (t : e |-- X ~= Y : s),
        P1 e X Y s t -> P1 e Y X s (tposr_eq_sym t)) ->
       (forall (e : lenv) (W X Y : lterm) s (t : e |-- W ~= X : s),
        P1 e W X s t ->
        forall t0 : e |-- X ~= Y : s,
        P1 e X Y s t0 -> P1 e W Y s (tposr_eq_trans t t0)) ->
       (forall (e : lenv) (A B : lterm) s (t : e |-- A -> A : s),
        P e A A s t ->
        forall t0 : e |-- B -> B : s,
        P e B B s t0 ->
        forall t1 : e |-- A ~= B : s,
        P1 e A B s t1 -> P2 e A B s (tposr_coerce_conv t t0 t1)) ->
       (forall (e : lenv) (A B A' B' : lterm) s (t : e |-- A' >-> A : s),
        P2 e A' A s t ->
        forall t0 : e |-- A' -> A' : s,
        P e A' A' s t0 ->
        forall t1 : e |-- A -> A : s,
        P e A A s t1 ->
        forall s' (t2 : A' :: e |-- B >-> B' : s'),
        P2 (A' :: e) B B' s' t2 ->
        forall t3 : A :: e |-- B -> B : s',
        P (A :: e) B B s' t3 ->
        forall t4 : A' :: e |-- B' -> B' : s',
        P (A' :: e) B' B' s' t4 ->
        P2 e (Prod_l A B) (Prod_l A' B') s'
          (tposr_coerce_prod t t0 t1 t2 t3 t4)) ->
       (forall (e : lenv) (A B A' B' : lterm) s (t : e |-- A >-> A' : s),
        P2 e A A' s t ->
        forall t0 : e |-- A' -> A' : s,
        P e A' A' s t0 ->
        forall t1 : e |-- A -> A : s,
        P e A A s t1 ->
        forall s' (t2 : A :: e |-- B >-> B' : s'),
        P2 (A :: e) B B' s' t2 ->
        forall t3 : A :: e |-- B -> B : s',
        P (A :: e) B B s' t3 ->
        forall t4 : A' :: e |-- B' -> B' : s',
        P (A' :: e) B' B' s' t4 ->
        forall s'' (s0 s1 : sum_sort s s' s''),
        P2 e (Sum_l A B) (Sum_l A' B') s''
          (tposr_coerce_sum t t0 t1 t2 t3 t4 s0 s1)) ->
       (forall (e : lenv) (U P3 U' : lterm) (t : e |-- U >-> U' : set),
        P2 e U U' set t ->
        forall t0 : e |-- U -> U : set,
        P e U U set t0 ->
        forall t1 : e |-- U' -> U' : set,
        P e U' U' set t1 ->
        forall t2 : U :: e |-- P3 -> P3 : prop,
        P (U :: e) P3 P3 prop t2 ->
        P2 e (Subset_l U P3) U' set (tposr_coerce_sub_l t t0 t1 t2)) ->
       (forall (e : lenv) (U U' P3 : lterm) (t : e |-- U >-> U' : set),
        P2 e U U' set t ->
        forall t0 : e |-- U -> U : set,
        P e U U set t0 ->
        forall t1 : e |-- U' -> U' : set,
        P e U' U' set t1 ->
        forall t2 : U' :: e |-- P3 -> P3 : prop,
        P (U' :: e) P3 P3 prop t2 ->
        P2 e U (Subset_l U' P3) set (tposr_coerce_sub_r t t0 t1 t2)) ->
       (forall (e : lenv) (U V : lterm) s (t : e |-- U >-> V : s),
        P2 e U V s t -> P2 e V U s (tposr_coerce_sym t)) ->
       (forall (e : lenv) (A B C : lterm) s (t : e |-- A >-> B : s),
        P2 e A B s t ->
        forall t0 : e |-- B >-> C : s,
        P2 e B C s t0 -> P2 e A C s (tposr_coerce_trans t t0)) ->


       (forall (l : lenv) (l0 l1 l2 : lterm) (t : l |-- l0 -> l1 : l2),
       P l l0 l1 l2 t) /\
       (forall (l : lenv) (t : tposr_wf l), P0 l t) /\
       (forall (l : lenv) (l0 l1 : lterm) (s : sort) (t : l |-- l0 ~= l1 : s),
       P1 l l0 l1 s t) /\
       (forall (l : lenv) (l0 l1 : lterm) (s : sort) (t : l |-- l0 >-> l1 : s),
       P2 l l0 l1 s t).
Proof.
  intros.
  split.
  intros.
  eapply tposr_mutind with (P := P) (P0 := P0) (P1 := P1) (P2 := P2); auto ; auto.
  split ;intros.
  eapply wf_mutind with (P := P) (P0 := P0) (P1 := P1) (P2 := P2) ; auto ; auto.
  split ; intros.
  eapply eq_mutind with (P := P) (P0 := P0) (P1 := P1) (P2 := P2) ; auto ; auto.
  eapply coerce_mutind with (P := P) (P0 := P0) (P1 := P1) (P2 := P2) ; auto ; auto.
Qed.

Lemma wf_tposr : forall e M N T, e |-- M -> N : T -> tposr_wf e.
Proof.
  induction 1 ; simpl ; auto with coc.
Qed.

Hint Resolve wf_tposr : ecoc.

Reserved Notation "G |-- M -+> N : B" (at level 70, M, N, B at next level). 

Inductive tposrp : lenv -> lterm -> lterm -> lterm -> Prop :=
  | tposrp_tposr : forall e X Y Z, e |-- X -> Y : Z -> e |-- X -+> Y : Z
  | tposrp_trans : forall e W X Y Z, e |-- W -+> X : Z -> e |-- X -+> Y : Z ->
  e |-- W -+> Y : Z

where "G |-- M -+> N : B" := (tposrp G M N B). 

Hint Resolve tposrp_tposr : coc.
Hint Resolve tposrp_trans : ecoc.

Definition tposr_term G M A := exists M', G |-- M -> M' : A.

Lemma tposr_tposr_term : forall G M M' A, tposr G M M' A -> tposr_term G M A.
Proof.
intros ; exists M' ; auto.
Qed.

Hint Resolve tposr_tposr_term : ecoc.
