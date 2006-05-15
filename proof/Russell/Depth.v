Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Substitution.
Require Import Coq.Arith.Max.
Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Reserved Notation "G |- T >>> U : s [ n ]" (at level 70, T, U, s, n at next level).

Inductive coerces_db : env -> term -> term -> sort -> nat -> Prop :=
  | coerces_refl : forall e A s, e |- A : Srt s -> e |- A >>> A : s [ 0 ]

  | coerces_prod : forall e A B A' B',
  forall s n, e |- A' >>> A : s [n]->
  (* derivable *) e |- A' : Srt s -> e |- A : Srt s ->
  forall s' m, (A' :: e) |- B >>> B' : s' [m] ->
  (* derivable *) A :: e |- B : Srt s' -> A' :: e |- B' : Srt s' ->
  e |- (Prod A B) >>> (Prod A' B') : s' [S (max n m)]

  | coerces_sum : forall e A B A' B',
  forall s n, e |- A >>> A' : s [n]->
  (* derivable *) e |- A' : Srt s -> e |- A : Srt s ->
  forall s' m, (A :: e) |- B >>> B' : s' [m] ->
  (* derivable *) A :: e |- B : Srt s' -> A' :: e |- B' : Srt s' ->
  sum_sort A B s s' -> sum_sort A' B' s s' ->
  e |- (Sum A B) >>> (Sum A' B') : s' [S (max n m)]

  | coerces_sub_l : forall e U P U' n,
  e |- U >>> U' : set [n]->
  (* derivable *) U :: e |- P : Srt prop ->
  e |- Subset U P >>> U' : set [S n]

  | coerces_sub_r : forall e U U' P n,
  e |- U >>> U' : set [n]->
  (* derivable *) U' :: e |- P : Srt prop ->
  e |- U >>> (Subset U' P) : set [S n]

  | coerces_conv_l : forall e A B C s n,
  e |- A : Srt s -> e |- B : Srt s -> e |- C : Srt s ->
  conv A B -> e |- B >>> C : s [n]-> e |- A >>> C : s [S n]

  | coerces_conv_r : forall e A B C s n,
  e |- A : Srt s -> e |- B : Srt s -> e |- C : Srt s ->
  e |- A >>> B : s [n] -> conv B C -> e |- A >>> C : s [S n]

where "G |- T >>> U : s [ n ]" := (coerces_db G T U s n).

Hint Resolve coerces_refl coerces_prod coerces_sum coerces_sub_l coerces_sub_r : coc.
Hint Resolve coerces_conv_l coerces_conv_r : coc.

Scheme coerces_db_dep := Induction for coerces_db Sort Prop.

Lemma coerce_coerces_db : forall G T U s, G |- T >> U : s -> exists n, G |- T >>> U : s [n].
Proof.
  induction 1 ; intros ; auto with coc core.
  exists 0 ; auto with coc.

  destruct IHcoerce1 as [n d1n] ; destruct IHcoerce2 as [m d2m].
  exists (S (max n m)) ; auto with coc.
  apply coerces_prod with s ; auto with coc.

  destruct IHcoerce1 as [n d1n] ; destruct IHcoerce2 as [m d2m].
  exists (S (max n m)) ; auto with coc.
  apply coerces_sum with s ; auto with coc.

  destruct IHcoerce as [n d1n].
  exists (S n) ; auto with coc.

  destruct IHcoerce as [n d1n].
  exists (S n) ; auto with coc.

  destruct IHcoerce as [n d1n].
  exists (S (S n)) ; auto with coc.

  apply coerces_conv_l with B ; auto with coc.
  apply coerces_conv_r with C ; auto with coc.
Qed.

Lemma coerces_db_coerce : forall G T U s n, G |- T >>> U : s [n] -> G |- T >> U : s.
Proof.
  induction 1 ; intros ; auto with coc core.

  apply coerce_prod with s; auto with coc.
  
  apply coerce_sum with s; auto with coc.

  apply coerce_conv with B C ; auto with coc.
  apply coerce_conv with A B ; auto with coc.
Qed.

Inductive coerce_in_env : env -> env -> Prop :=
  | coerce_env_hd : forall e t u s n, e |- t >>> u : s [n] -> 
	coerce_in_env (u :: e) (t :: e)
  | coerce_env_tl :
        forall e f t, wf (t :: f) -> coerce_in_env e f -> coerce_in_env (t :: e) (t :: f).

Hint Resolve coerce_env_hd coerce_env_tl: coc.

Axiom typ_conv_env :
  forall e t T, forall d : (e |- t : T),
  forall f, coerce_in_env e f -> 
  wf f -> f |- t : T.

Axiom coerce_conv_env :
  forall e T U s n, 
  e |- T >>> U : s [n] -> 
  forall f, coerce_in_env e f -> 
  wf f ->  f |- T >>> U : s [n].

