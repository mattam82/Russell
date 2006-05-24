Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import TPOSR.Terms.
Require Import TPOSR.Reduction.
Require Import TPOSR.Conv.
Require Import TPOSR.LiftSubst.
Require Import TPOSR.Env.

Set Implicit Arguments.

Reserved Notation "G |- u -> v : T [ n ]" (at level 70, u, v, T, n at next level).

Definition sum_sort s1 s2 s3 :=
  (s1 = set /\ s2 = set /\ s3 = set) \/
  (s1 = prop /\ s2 = prop /\ s3 = prop).

Require Import Coq.Arith.Max.

Definition max3 n m p := max n (max m p).
Definition max4 n m p q := max n (max m (max p q)).

Inductive tposrd_wf : lenv -> Prop :=
  | wf_nil : tposrd_wf nil
  | wf_cons : forall G A A' s n, G |- A -> A' : Srt_l s [n] -> tposrd_wf (A :: G)

with tposrd : lenv -> lterm -> lterm -> lterm -> nat -> Prop :=
  | tposrd_var : forall e, tposrd_wf e -> 
  forall n T, item_llift T e n -> e |- (Ref_l n) -> (Ref_l n) : T [0]

  | tposrd_set : forall e, tposrd_wf e -> e |- (Srt_l set) -> (Srt_l set) : Srt_l kind [0]
  | tposrd_prop : forall e, tposrd_wf e -> e |- (Srt_l prop) -> (Srt_l prop) : Srt_l kind [0]

  | tposrd_prod : forall e A A' s1 n, e |- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |- B -> B' : Srt_l s2 [m] ->
  e |- Prod_l A B -> Prod_l A' B' : Srt_l s2 [S (max n m)]
  
  | tposrd_abs : forall e A A' s1 n, e |- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |- B -> B' : Srt_l s2 [m] ->
  forall M M' p, (A :: e) |- M -> M' : B [p] -> 
  e |- Abs_l A M -> Abs_l A' M' : (Prod_l A B) [S (max3 n m p)]
  
  | tposrd_app : forall e A A' s1 n, e |- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |- B -> B' : Srt_l s2 [m] ->
  forall M M' p, e |- M -> M' : (Prod_l A B) [p] -> 
  forall N N' q, e |- N -> N' : A [q] ->
  e |- App_l B M N -> App_l B' M' N' : lsubst N B [S (max4 n m p q)]

  | tposrd_beta : forall e A A' s1 n, e |- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |- B -> B' : Srt_l s2 [m] ->
  forall M M' p, (A :: e) |- M -> M' : B [p] -> 
  forall N N' q, e |- N -> N' : A [q] ->
  e |- App_l B (Abs_l A M) N -> lsubst N' M' : lsubst N B [S (max4 n m p q)]

  | tposrd_red : forall e M N A n, e |- M -> N : A [n] -> 
  forall B s m, e |- A -> B : Srt_l s [m] ->
  e |- M -> N : B [S (max n m)]
  
  | tposrd_exp : forall e M N B n, e |- M -> N : B [n] -> 
  forall A s m, e |- A -> B : Srt_l s [m] ->
  e |- M -> N : A [S (max n m)]
  
  | tposrd_subset : forall e A A' n, e |- A -> A' : Srt_l set [n] ->
  forall B B' m, (A :: e) |- B -> B' : Srt_l prop [m] ->
  e |- Subset_l A B -> Subset_l A' B' : Srt_l set [S (max n m)]

  | tposrd_sum : forall e A A' s1 n, e |- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |- B -> B' : Srt_l s2 [m] ->
  forall s3, sum_sort s1 s2 s3 ->
  e |- Sum_l A B -> Sum_l A' B' : Srt_l s3 [S (max n m)]
  
  | tposrd_pi1 : forall e A A' s1 n, e |- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |- B -> B' : Srt_l s2 [m] ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t' p, e |- t -> t' : Sum_l A B [p] ->
  e |- Pi1_l t -> Pi1_l t' : A [S (max3 n m p)]

  | tposrd_pi1_red : forall e A A' s1 n, e |- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |- B -> B' : Srt_l s2 [m] ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v' p, e |- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B [p] ->
  e |- Pi1_l (Pair_l (Sum_l A B) u v) -> u : A [S (max3 n m p)]

  | tposrd_pi2 : forall e A A' s1 n, e |- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |- B -> B' : Srt_l s2 [m] ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t' p, e |- t -> t' : Sum_l A B [p] ->
  e |- Pi2_l t -> Pi2_l t' : lsubst (Pi1_l t) B [S (max3 n m p)]

  | tposrd_pi2_red : forall e A A' s1 n, e |- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |- B -> B' : Srt_l s2 [m] ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v' p, 
  e |- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B [p] ->
  e |- Pi2_l (Pair_l (Sum_l A B) u v) -> v : lsubst (Pi1_l (Pair_l (Sum_l A B) u v)) B
  [S (max3 n m p)]

where "G |- T -> U : s [ n ]" := (tposrd G T U s n).

Hint Resolve wf_nil tposrd_set tposrd_prop : coc.

Scheme ind_tposr := Induction for tposrd Sort Prop.

Scheme tposrd_wf_mutind := Induction for tposrd Sort Prop
with wf_tposrd_mutind :=  Induction for tposrd_wf Sort Prop.

Require Import TPOSR.Types.

Ltac double_ind pred :=
  match goal with 
  | |- ?A /\ ?B => apply (pred A B)
  end.



Lemma tposr_tposrd : 
  (forall e t u T, tposr e t u T -> 
  exists n, e |- t -> u : T [n]) /\
  (forall e, tposr_wf e -> tposrd_wf e).
Proof.
  apply ind_tposr_wf with
  (P := fun e t u T => fun H : tposr e t u T =>
  exists n, e |- t -> u : T [n])
  (P0 := fun e => fun H : tposr_wf e => tposrd_wf e)
  ; simpl ; intros ; auto with coc ; auto with coc.

  exists 0 ; constructor ; auto with coc.
  exists 0 ; constructor ; auto with coc.
  exists 0 ; constructor ; auto with coc.
  
  intuition.
  exists (S (max n m)) ; constructor ; auto with coc.





Check tposrd_wf_mutind.

Lemma ind_tposrd_wf :