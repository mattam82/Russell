Require Import Lambda.Tactics.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.

Set Implicit Arguments.

Reserved Notation "G |-- u -> v : T [ n ]" (at level 70, u, v, T, n at next level).

Require Import Lambda.TPOSR.MaxLemmas.

Inductive tposrd_wf : lenv -> Prop :=
  | wfd_nil : tposrd_wf nil
  | wfd_cons : forall G A A' s n, G |-- A -> A' : Srt_l s [n] -> tposrd_wf (A :: G)

with tposrd : lenv -> lterm -> lterm -> lterm -> nat -> Prop :=
  | tposrd_var : forall e, tposrd_wf e -> 
  forall n T, item_llift T e n -> e |-- (Ref_l n) -> (Ref_l n) : T [0]

  | tposrd_set : forall e, tposrd_wf e -> e |-- (Srt_l set) -> (Srt_l set) : Srt_l kind [0]
  | tposrd_prop : forall e, tposrd_wf e -> e |-- (Srt_l prop) -> (Srt_l prop) : Srt_l kind [0]

  | tposrd_prod : forall e A A' s1 n, e |-- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |-- B -> B' : Srt_l s2 [m] ->
  e |-- Prod_l A B -> Prod_l A' B' : Srt_l s2 [S (max n m)]
  
  | tposrd_abs : forall e A A' s1 n, e |-- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |-- B -> B' : Srt_l s2 [m] ->
  forall M M' p, (A :: e) |-- M -> M' : B [p] -> 
  e |-- Abs_l A M -> Abs_l A' M' : (Prod_l A B) [S (max3 n m p)]
  
  | tposrd_app : forall e A A' s1 n, e |-- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |-- B -> B' : Srt_l s2 [m] ->
  forall M M' p, e |-- M -> M' : (Prod_l A B) [p] -> 
  forall N N' q, e |-- N -> N' : A [q] ->
  e |-- App_l B M N -> App_l B' M' N' : lsubst N B [S (max4 n m p q)]

  | tposrd_beta : forall e A A' s1 n, e |-- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |-- B -> B' : Srt_l s2 [m] ->
  forall M M' p, (A :: e) |-- M -> M' : B [p] -> 
  forall N N' q, e |-- N -> N' : A [q] ->
  e |-- App_l B (Abs_l A M) N -> lsubst N' M' : lsubst N B [S (max4 n m p q)]

  | tposrd_red : forall e M N A n, e |-- M -> N : A [n] -> 
  forall B s m, e |-- A -> B : Srt_l s [m] ->
  e |-- M -> N : B [S (max n m)]
  
  | tposrd_exp : forall e M N B n, e |-- M -> N : B [n] -> 
  forall A s m, e |-- A -> B : Srt_l s [m] ->
  e |-- M -> N : A [S (max n m)]
  
  | tposrd_subset : forall e A A' n, e |-- A -> A' : Srt_l set [n] ->
  forall B B' m, (A :: e) |-- B -> B' : Srt_l prop [m] ->
  e |-- Subset_l A B -> Subset_l A' B' : Srt_l set [S (max n m)]

  | tposrd_sum : forall e A A' s1 n, e |-- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |-- B -> B' : Srt_l s2 [m] ->
  forall s3, sum_sort s1 s2 s3 ->
  e |-- Sum_l A B -> Sum_l A' B' : Srt_l s3 [S (max n m)]

 | tposrd_pair : forall e A A' s1 n, e |-- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |-- B -> B' : Srt_l s2 [m] ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' p, e |-- u -> u' : A [p] ->
  forall v v' q, e |-- v -> v' : lsubst u B [q] ->
  e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B [S (max4 n m p q)]

  | tposrd_pi1 : forall e A A' s1 n, e |-- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |-- B -> B' : Srt_l s2 [m] ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t' p, e |-- t -> t' : Sum_l A B [p] ->
  e |-- Pi1_l (Sum_l A B) t -> Pi1_l (Sum_l A' B') t' : A [S (max3 n m p)]

  | tposrd_pi1_red : forall e A A' s1 n, e |-- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |-- B -> B' : Srt_l s2 [m] ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v' p, e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B [p] ->
  forall A'', e |-- A'' ~= A : s1 ->
  forall B'', A'' :: e |-- B'' ~= B : s2 ->
  e |-- Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v) -> u' : A'' [S (max3 n m p)]

  | tposrd_pi2 : forall e A A' s1 n, e |-- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |-- B -> B' : Srt_l s2 [m] ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t' p, e |-- t -> t' : Sum_l A B [p] ->
  e |-- Pi2_l (Sum_l A B) t -> Pi2_l (Sum_l A' B') t' : lsubst (Pi1_l (Sum_l A B) t) B [S (max3 n m p)]

  | tposrd_pi2_red : forall e A A' s1 n, e |-- A -> A' : Srt_l s1 [n] ->
  forall B B' s2 m, (A :: e) |-- B -> B' : Srt_l s2 [m] ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v' p, 
  e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v' : Sum_l A B [p] ->
  e |-- Pi2_l (Sum_l A B) (Pair_l (Sum_l A B) u v) -> v' : lsubst (Pi1_l (Sum_l A B) (Pair_l (Sum_l A B) u v)) B
  [S (max3 n m p)]

where "G |-- T -> U : s [ n ]" := (tposrd G T U s n).

Hint Resolve wfd_nil tposrd_set tposrd_prop tposrd_subset : coc.
Hint Resolve tposrd_prod tposrd_abs tposrd_app tposrd_sum  : coc.

Scheme ind_tposr := Induction for tposrd Sort Prop.

Scheme tposrd_wf_mutind := Induction for tposrd Sort Prop
with wf_tposrd_mutind :=  Induction for tposrd_wf Sort Prop.

Require Import Lambda.TPOSR.Types.

Lemma tposr_tposrd : 
  (forall e t u T, tposr e t u T -> 
  exists n, e |-- t -> u : T [n]) /\
  (forall e, tposr_wf e -> tposrd_wf e).
Proof.
  apply ind_tposr_wf with
  (P := fun e t u T => fun H : tposr e t u T =>
  exists n, e |-- t -> u : T [n])
  (P0 := fun e => fun H : tposr_wf e => tposrd_wf e)
  ; simpl ; intros ; auto with coc  ; intuition  ; destruct_exists ; auto with coc.

  exists 0 ; constructor ; auto with coc.
  exists 0 ; constructor ; auto with coc.
  exists 0 ; constructor ; auto with coc.
  
  exists (S (max x0 x)) ; apply tposrd_prod with s1 ; auto with coc.

  exists (S (max3 x1 x0 x)) ; apply tposrd_abs with s1 B' s2 ; auto with coc.

  exists (S (max4 x2 x1 x0 x)) ; apply tposrd_app with A A' s1 s2 ; auto with coc.

  exists (S (max4 x2 x1 x0 x)) ; apply tposrd_beta with A' s1 B' s2 ; auto with coc.

  exists (S (max x0 x)) ; apply tposrd_red with A s ; auto with coc.

  exists (S (max x0 x)) ; apply tposrd_exp with B s ; auto with coc.

  exists (S (max x0 x)) ; apply tposrd_subset  ; auto with coc.

  exists (S (max x0 x)) ; apply tposrd_sum with s1 s2 ; auto with coc.

  exists (S (max4 x2 x1 x0 x)) ; apply tposrd_pair with s1 s2 s3 ; auto with coc.

  exists (S (max3 x1 x0 x)) ; apply tposrd_pi1 with s1 s2 s3 ; auto with coc.

  exists (S (max3 x1 x0 x)) ; apply tposrd_pi1_red with A' s1 B' s2 s3 v' ; auto with coc.

  exists (S (max3 x1 x0 x)) ; apply tposrd_pi2 with s1 s2 s3 ; auto with coc.

  exists (S (max3 x1 x0 x)) ; apply tposrd_pi2_red with A' s1 B' s2 s3 u' ; auto with coc.

  apply wfd_cons with A' s x; auto with coc.
Qed.

Corollary tposr_tposrd_type : forall e t u T, tposr e t u T -> 
  exists n, e |-- t -> u : T [n].
Proof (proj1 tposr_tposrd).

Corollary tposr_tposrd_wf : forall e, tposr_wf e -> tposrd_wf e.
Proof (proj2 tposr_tposrd).

Check tposrd_wf_mutind.

Lemma ind_tposrd_wf :
forall
         (P : forall (l : lenv) (l0 l1 l2 : lterm) (n : nat),
              l |-- l0 -> l1 : l2 [n] -> Prop)
         (P0 : forall l : lenv, tposrd_wf l -> Prop),
       (forall (e : lenv) (t : tposrd_wf e),
        P0 e t ->
        forall (n : nat) (T : lterm) (i : item_llift T e n),
        P e (Ref_l n) (Ref_l n) T 0 (tposrd_var t i)) ->
       (forall (e : lenv) (t : tposrd_wf e),
        P0 e t -> P e (Srt_l set) (Srt_l set) (Srt_l kind) 0 (tposrd_set t)) ->
       (forall (e : lenv) (t : tposrd_wf e),
        P0 e t ->
        P e (Srt_l prop) (Srt_l prop) (Srt_l kind) 0 (tposrd_prop t)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort) (n : nat)
          (t : e |-- A -> A' : Srt_l s1 [n]),
        P e A A' (Srt_l s1) n t ->
        forall (B B' : lterm) (s2 : sort) (m : nat)
          (t0 : A :: e |-- B -> B' : Srt_l s2 [m]),
        P (A :: e) B B' (Srt_l s2) m t0 ->
        P e (Prod_l A B) (Prod_l A' B') (Srt_l s2) (S (max n m))
          (tposrd_prod t t0)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort) (n : nat)
          (t : e |-- A -> A' : Srt_l s1 [n]),
        P e A A' (Srt_l s1) n t ->
        forall (B B' : lterm) (s2 : sort) (m : nat)
          (t0 : A :: e |-- B -> B' : Srt_l s2 [m]),
        P (A :: e) B B' (Srt_l s2) m t0 ->
        forall (M M' : lterm) (p : nat) (t1 : A :: e |-- M -> M' : B [p]),
        P (A :: e) M M' B p t1 ->
        P e (Abs_l A M) (Abs_l A' M') (Prod_l A B) (S (max3 n m p))
          (tposrd_abs t t0 t1)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort) (n : nat)
          (t : e |-- A -> A' : Srt_l s1 [n]),
        P e A A' (Srt_l s1) n t ->
        forall (B B' : lterm) (s2 : sort) (m : nat)
          (t0 : A :: e |-- B -> B' : Srt_l s2 [m]),
        P (A :: e) B B' (Srt_l s2) m t0 ->
        forall (M M' : lterm) (p : nat) (t1 : e |-- M -> M' : Prod_l A B [p]),
        P e M M' (Prod_l A B) p t1 ->
        forall (N N' : lterm) (q : nat) (t2 : e |-- N -> N' : A [q]),
        P e N N' A q t2 ->
        P e (App_l B M N) (App_l B' M' N') (lsubst N B) (S (max4 n m p q))
          (tposrd_app t t0 t1 t2)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort) (n : nat)
          (t : e |-- A -> A' : Srt_l s1 [n]),
        P e A A' (Srt_l s1) n t ->
        forall (B B' : lterm) (s2 : sort) (m : nat)
          (t0 : A :: e |-- B -> B' : Srt_l s2 [m]),
        P (A :: e) B B' (Srt_l s2) m t0 ->
        forall (M M' : lterm) (p : nat) (t1 : A :: e |-- M -> M' : B [p]),
        P (A :: e) M M' B p t1 ->
        forall (N N' : lterm) (q : nat) (t2 : e |-- N -> N' : A [q]),
        P e N N' A q t2 ->
        P e (App_l B (Abs_l A M) N) (lsubst N' M') (lsubst N B)
          (S (max4 n m p q)) (tposrd_beta t t0 t1 t2)) ->
       (forall (e : lenv) (M N A : lterm) (n : nat)
          (t : e |-- M -> N : A [n]),
        P e M N A n t ->
        forall (B : lterm) (s : sort) (m : nat)
          (t0 : e |-- A -> B : Srt_l s [m]),
        P e A B (Srt_l s) m t0 -> P e M N B (S (max n m)) (tposrd_red t t0)) ->
       (forall (e : lenv) (M N B : lterm) (n : nat)
          (t : e |-- M -> N : B [n]),
        P e M N B n t ->
        forall (A : lterm) (s : sort) (m : nat)
          (t0 : e |-- A -> B : Srt_l s [m]),
        P e A B (Srt_l s) m t0 -> P e M N A (S (max n m)) (tposrd_exp t t0)) ->
       (forall (e : lenv) (A A' : lterm) (n : nat)
          (t : e |-- A -> A' : Srt_l set [n]),
        P e A A' (Srt_l set) n t ->
        forall (B B' : lterm) (m : nat)
          (t0 : A :: e |-- B -> B' : Srt_l prop [m]),
        P (A :: e) B B' (Srt_l prop) m t0 ->
        P e (Subset_l A B) (Subset_l A' B') (Srt_l set) (S (max n m))
          (tposrd_subset t t0)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort) (n : nat)
          (t : e |-- A -> A' : Srt_l s1 [n]),
        P e A A' (Srt_l s1) n t ->
        forall (B B' : lterm) (s2 : sort) (m : nat)
          (t0 : A :: e |-- B -> B' : Srt_l s2 [m]),
        P (A :: e) B B' (Srt_l s2) m t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3),
        P e (Sum_l A B) (Sum_l A' B') (Srt_l s3) (S (max n m))
          (tposrd_sum t t0 s)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort) (n : nat)
          (t : e |-- A -> A' : Srt_l s1 [n]),
        P e A A' (Srt_l s1) n t ->
        forall (B B' : lterm) (s2 : sort) (m : nat)
          (t0 : A :: e |-- B -> B' : Srt_l s2 [m]),
        P (A :: e) B B' (Srt_l s2) m t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (u u' : lterm) (p : nat)
          (t1 : e |-- u -> u' : A [p]),
        P e u u' A p t1 ->
        forall (v v' : lterm) (q : nat) (t2 : e |-- v -> v' : lsubst u B [q]),
        P e v v' (lsubst u B) q t2 ->
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          (S (max4 n m p q)) (tposrd_pair t t0 s t1 t2)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort) (n : nat)
          (t : e |-- A -> A' : Srt_l s1 [n]),
        P e A A' (Srt_l s1) n t ->
        forall (B B' : lterm) (s2 : sort) (m : nat)
          (t0 : A :: e |-- B -> B' : Srt_l s2 [m]),
        P (A :: e) B B' (Srt_l s2) m t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (t1 t' : lterm) (p : nat)
          (t2 : e |-- t1 -> t' : Sum_l A B [p]),
        P e t1 t' (Sum_l A B) p t2 ->
        P e (Pi1_l (Sum_l A B) t1) (Pi1_l (Sum_l A' B') t') A
          (S (max3 n m p)) (tposrd_pi1 t t0 s t2)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort) (n : nat)
          (t : e |-- A -> A' : Srt_l s1 [n]),
        P e A A' (Srt_l s1) n t ->
        forall (B B' : lterm) (s2 : sort) (m : nat)
          (t0 : A :: e |-- B -> B' : Srt_l s2 [m]),
        P (A :: e) B B' (Srt_l s2) m t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (u u' v v' : lterm)
          (p : nat)
          (t1 : e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v'
                : Sum_l A B [p]),
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          p t1 ->
        forall (A'' : lterm) (t2 : e |-- A'' ~= A : s1) (B'' : lterm)
          (t3 : A'' :: e |-- B'' ~= B : s2),
        P e (Pi1_l (Sum_l A'' B'') (Pair_l (Sum_l A B) u v)) u' A''
          (S (max3 n m p)) (tposrd_pi1_red t t0 s t1 t2 t3)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort) (n : nat)
          (t : e |-- A -> A' : Srt_l s1 [n]),
        P e A A' (Srt_l s1) n t ->
        forall (B B' : lterm) (s2 : sort) (m : nat)
          (t0 : A :: e |-- B -> B' : Srt_l s2 [m]),
        P (A :: e) B B' (Srt_l s2) m t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (t1 t' : lterm) (p : nat)
          (t2 : e |-- t1 -> t' : Sum_l A B [p]),
        P e t1 t' (Sum_l A B) p t2 ->
        P e (Pi2_l (Sum_l A B) t1) (Pi2_l (Sum_l A' B') t')
          (lsubst (Pi1_l (Sum_l A B) t1) B) (S (max3 n m p))
          (tposrd_pi2 t t0 s t2)) ->
       (forall (e : lenv) (A A' : lterm) (s1 : sort) (n : nat)
          (t : e |-- A -> A' : Srt_l s1 [n]),
        P e A A' (Srt_l s1) n t ->
        forall (B B' : lterm) (s2 : sort) (m : nat)
          (t0 : A :: e |-- B -> B' : Srt_l s2 [m]),
        P (A :: e) B B' (Srt_l s2) m t0 ->
        forall (s3 : sort) (s : sum_sort s1 s2 s3) (u u' v v' : lterm)
          (p : nat)
          (t1 : e |-- Pair_l (Sum_l A B) u v -> Pair_l (Sum_l A' B') u' v'
                : Sum_l A B [p]),
        P e (Pair_l (Sum_l A B) u v) (Pair_l (Sum_l A' B') u' v') (Sum_l A B)
          p t1 ->
        P e (Pi2_l (Sum_l A B) (Pair_l (Sum_l A B) u v)) v'
          (lsubst (Pi1_l (Sum_l A B) (Pair_l (Sum_l A B) u v)) B)
          (S (max3 n m p)) (tposrd_pi2_red t t0 s t1)) ->
       P0 nil wfd_nil ->
       (forall (G : lenv) (A A' : lterm) (s : sort) (n : nat)
          (t : G |-- A -> A' : Srt_l s [n]),
        P G A A' (Srt_l s) n t -> P0 (A :: G) (wfd_cons t)) ->
       (forall (l : lenv) (l0 l1 l2 : lterm) (n : nat)
         (t : l |-- l0 -> l1 : l2 [n]), P l l0 l1 l2 n t)
      /\ (forall (l : lenv) (t : tposrd_wf l), P0 l t).
Proof.
  intros ; split ; intros.
  apply tposrd_wf_mutind with (P:=P) (P0:=P0) ; auto ; auto.
  apply wf_tposrd_mutind with (P:=P) (P0:=P0) ; auto ; auto.
Qed.

Lemma tposrd_tposr : 
  (forall e t u T n, tposrd e t u T n -> 
  tposr e t u T) /\
  (forall e, tposrd_wf e -> tposr_wf e).
Proof.
  apply ind_tposrd_wf with
  (P := fun e t u T n => fun H : tposrd e t u T n =>
  e |-- t -> u : T)
  (P0 := fun e => fun H : tposrd_wf e => tposr_wf e)
  ; simpl ; intros ; auto with coc  ; intuition  ; destruct_exists ; auto with coc.

  apply tposr_prod with s1 ; auto with coc.

  apply tposr_abs with s1 B' s2 ; auto with coc.

  apply tposr_app with A A' s1 s2 ; auto with coc.

  apply tposr_beta with A' s1 B' s2 ; auto with coc.
  
  apply tposr_red with A s ; auto with coc.

  apply tposr_exp with B s ; auto with coc.

  apply tposr_sum with s1 s2 ; auto with coc.
  
  apply tposr_pair with s1 s2 s3 ; auto with coc.

  apply tposr_pi1 with s1 s2 s3 ; auto with coc.

  apply tposr_pi1_red with A' s1 B' s2 s3 v' ; auto with coc.

  apply tposr_pi2 with s1 s2 s3; auto with coc.

  apply tposr_pi2_red with A' s1 B' s2 s3 u'; auto with coc.

  apply wf_cons with A' s ; auto with coc.
Qed.

Corollary tposrd_tposr_type : forall e t u T n, e |-- t -> u : T [n] -> 
  e |-- t -> u : T.
Proof (proj1 tposrd_tposr).

Corollary tposrd_tposr_wf : forall e, tposrd_wf e -> tposr_wf e.
Proof (proj2 tposrd_tposr).

Hint Resolve tposrd_tposr_type tposrd_tposr_wf : coc.

Lemma tposr_to_tposrd : forall (P : Prop) e t u T n, e |-- t -> u : T [n] ->
  (e |-- t -> u : T -> P) -> P.
Proof.
  intros ; auto with coc.
  apply H0 ; auto with coc.
  apply tposrd_tposr_type with n ; auto.
Qed.

Definition tposr_term_depth G M A := exists M', exists n, G |-- M -> M' : A [n].

Lemma tposr_term_tod : forall G M A, tposr_term G M A  -> tposr_term_depth G M A.
Proof.
  intros.
  unfold tposr_term in H ; destruct_exists.
  pose (tposr_tposrd_type H) ; destruct_exists.
  exists x ; exists x0 ; auto.
Qed.

Lemma tposr_term_fromd : forall G M A, tposr_term_depth G M A  -> tposr_term G M A.
Proof.
  intros.
  unfold tposr_term_depth in H ; destruct_exists.
  exists x.
  apply (tposrd_tposr_type H).
Qed.

Definition tod := tposr_tposrd_type.
Definition fromd := tposrd_tposr_type.
