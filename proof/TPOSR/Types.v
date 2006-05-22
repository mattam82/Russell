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

Reserved Notation "G |- T -> U : s" (at level 70, T, U, s at next level).

Definition sum_sort s1 s2 s3 :=
  (s1 = set /\ s2 = set /\ s3 = set) \/
  (s1 = prop /\ s2 = prop /\ s3 = prop).

Inductive tposr_wf : lenv -> Prop :=
  | wf_nil : tposr_wf nil
  | wf_cons : forall G A A' s, G |- A -> A' : Srt_l s -> tposr_wf (A :: G)

with tposr : lenv -> lterm -> lterm -> lterm -> Prop :=
  | tposr_var : forall e, tposr_wf e -> 
  forall n T, item_llift T e n -> e |- (Ref_l n) -> (Ref_l n) : T

  | tposr_set : forall e, tposr_wf e -> e |- (Srt_l set) -> (Srt_l set) : Srt_l kind
  | tposr_prop : forall e, tposr_wf e -> e |- (Srt_l prop) -> (Srt_l prop) : Srt_l kind

  | tposr_prod : forall e A A' s1, e |- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |- B -> B' : Srt_l s2 ->
  e |- Prod_l A B -> Prod_l A' B' : Srt_l s2
  
  | tposr_abs : forall e A A' s1, e |- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |- B -> B' : Srt_l s2 ->
  forall M M', (A :: e) |- M -> M' : B -> 
  e |- Abs_l A M -> Abs_l A' M' : (Prod_l A B)
  
  | tposr_app : forall e A A' s1, e |- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |- B -> B' : Srt_l s2 ->
  forall M M', e |- M -> M' : (Prod_l A B) -> 
  forall N N', e |- N -> N' : A ->
  e |- App_l B M N -> App_l B' M' N' : lsubst N B

  | tposr_beta : forall e A A' s1, e |- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |- B -> B' : Srt_l s2 ->
  forall M M', (A :: e) |- M -> M' : B -> 
  forall N N', e |- N -> N' : A ->
  e |- App_l B (Abs_l A M) N -> lsubst N' M' : lsubst N B

  | tposr_red : forall e M N A, e |- M -> N : A -> 
  forall B s, e |- A -> B : Srt_l s ->
  e |- M -> N : B
  
  | tposr_exp : forall e M N B, e |- M -> N : B -> 
  forall A s, e |- A -> B : Srt_l s ->
  e |- M -> N : A
  
  | tposr_subset : forall e A A', e |- A -> A' : Srt_l set ->
  forall B B', (A :: e) |- B -> B' : Srt_l prop ->
  e |- Subset_l A B -> Subset_l A' B' : Srt_l set

  | tposr_sum : forall e A A' s1, e |- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  e |- Sum_l A B -> Sum_l A' B' : Srt_l s3
  
  | tposr_pi1 : forall e A A' s1, e |- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |- t -> t' : Sum_l A B ->
  e |- Pi1_l t -> Pi1_l t' : A

  | tposr_pi1_red : forall e A A' s1, e |- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', e |- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B ->
  e |- Pi1_l (Pair_l (Sum_l A B) u v) -> u : A

  | tposr_pi2 : forall e A A' s1, e |- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |- t -> t' : Sum_l A B ->
  e |- Pi2_l t -> Pi2_l t' : lsubst (Pi1_l t) B

  | tposr_pi2_red : forall e A A' s1, e |- A -> A' : Srt_l s1 ->
  forall B B' s2, (A :: e) |- B -> B' : Srt_l s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', 
  e |- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B ->
  e |- Pi2_l (Pair_l (Sum_l A B) u v) -> v : lsubst u B

where "G |- T -> U : s" := (tposr G T U s).

Inductive tposrp : lenv -> lterm -> lterm -> lterm -> Prop :=
  | tposrp_tposr : forall e X Y Z, e |- X -> Y : Z -> tposrp e X Y Z
  | tposrp_trans : forall e W X Y Z, tposrp e W X Z -> tposrp e X Y Z ->
  tposrp e W Y Z.

Reserved Notation "G |- T ~= U : s" (at level 70, T, U, s at next level).

Inductive tposr_eq : lenv -> lterm -> lterm -> sort -> Prop :=
  | tposr_eq_tposr : forall e X Y s, e |- X -> Y : Srt_l s -> e |- X ~= Y : s
  | tposr_eq_sym : forall e X Y s, e |- X ~= Y : s -> e |- Y ~= X : s
  | tposr_eq_trans : forall e W X Y s, e |- W ~= X : s -> e |- X ~= Y : s ->
  e |- W ~= Y : s

where "G |- T ~= U : s" := (tposr_eq G T U s).

Lemma tposr_conv : forall e A B s, e |- A ~= B : s -> 
  forall M N, (e |- M -> N : A -> e |- M -> N : B) /\ (e |- M -> N : B -> e |- M -> N : A).
Proof.
  induction 1 ; simpl ; intros.
  
  split ; intros.
  apply tposr_red with X s ; auto.
  apply tposr_exp with Y s ; auto.

  pose (IHtposr_eq M N).
  intuition ; auto with coc.

  pose (IHtposr_eq1 M N).
  pose (IHtposr_eq2 M N).
  intuition ; auto with coc.
Qed.

Lemma tposr_lred : forall e M N Z, e |- M -> N : Z -> lred M N.
Proof.
  induction 1 ; simpl ; auto with coc.

  apply trans_lred with (App_l B' (Abs_l A' M') N') ; auto with coc.
Qed.

Lemma tposr_eq_conv : forall e M N Z, e |- M ~= N : Z -> conv M N.
Proof.
  induction 1 ; simpl ; auto with coc.
  
  pose (tposr_lred H) ; auto with coc.
  apply trans_conv_conv with X ; auto with coc.
Qed.

Lemma wf_tposr : forall e M N T, e |- M -> N : T -> tposr_wf e.
Proof.
  induction 1 ; simpl ; auto with coc.
Qed.



  