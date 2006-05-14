Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Substitution.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Reserved Notation "G |- T >>> U : s" (at level 70, T, U, s at next level).

Inductive coerces_db : env -> term -> term -> sort -> Prop :=
  | coerces_refl : forall e A s, e |- A : Srt s -> e |- A >>> A : s

  | coerces_prod : forall e A B A' B',
  forall s, e |- A' >>> A : s ->
  (* derivable *) e |- A' : Srt s -> e |- A : Srt s ->
  forall s', (A' :: e) |- B >>> B' : s' ->
  (* derivable *) A :: e |- B : Srt s' -> A' :: e |- B' : Srt s' ->
  e |- (Prod A B) >>> (Prod A' B') : s'

  | coerces_sum : forall e A B A' B',
  forall s, e |- A >>> A' : s ->
  (* derivable *) e |- A' : Srt s -> e |- A : Srt s ->
  forall s', (A :: e) |- B >>> B' : s' ->
  (* derivable *) A :: e |- B : Srt s' -> A' :: e |- B' : Srt s' ->
  sum_sort A B s s' -> sum_sort A' B' s s' ->
  e |- (Sum A B) >>> (Sum A' B') : s'

  | coerces_sub_l : forall e U P U',
  e |- U >>> U' : set ->
  (* derivable *) U :: e |- P : Srt prop ->
  e |- Subset U P >>> U' : set

  | coerces_sub_r : forall e U U' P,
  e |- U >>> U' : set ->
  (* derivable *) U' :: e |- P : Srt prop ->
  e |- U >>> (Subset U' P) : set

  | coerces_conv_l : forall e A B C s,
  e |- A : Srt s -> e |- B : Srt s -> e |- C : Srt s ->
  conv A B -> e |- B >>> C : s -> e |- A >>> C : s

  | coerces_conv_r : forall e A B C s,
  e |- A : Srt s -> e |- B : Srt s -> e |- C : Srt s ->
  e |- A >>> B : s -> conv B C -> e |- A >>> C : s

where "G |- T >>> U : s" := (coerces_db G T U s).

Hint Resolve coerces_refl coerces_prod coerces_sum coerces_sub_l coerces_sub_r : coc.
Hint Resolve coerces_conv_l coerces_conv_r : coc.

Scheme coerces_db_dep := Induction for coerces_db Sort Prop.

Lemma coerce_coerces_db : forall G T U s, G |- T >> U : s -> G |- T >>> U : s.
Proof.
  induction 1 ; intros ; auto with coc core.

  apply coerces_prod with s; auto with coc.
  
  apply coerces_sum with s; auto with coc.

  apply coerces_conv_l with B ; auto with coc.
  apply coerces_conv_r with C ; auto with coc.
Qed.

Lemma coerces_db_coerce : forall G T U s, G |- T >>> U : s -> G |- T >> U : s.
Proof.
  induction 1 ; intros ; auto with coc core.

  apply coerce_prod with s; auto with coc.
  
  apply coerce_sum with s; auto with coc.

  apply coerce_conv with B C ; auto with coc.
  apply coerce_conv with A B ; auto with coc.
Qed.

Require Import Coq.Arith.Max.

Inductive depth : forall e T U s, e |- T >>> U : s -> nat -> Prop
 :=
  | depth_coerces_refl : forall e A s As, @depth e A A s (coerces_refl As) 0

  | depth_coerces_prod : forall e A B A' B' s HsubA A's As s' HsubBB' Bs B's, 
    forall n m, depth HsubA n -> depth HsubBB' m ->
    @depth e (Prod A B) (Prod A' B') s' (@coerces_prod e A B A' B' s HsubA A's As s' HsubBB' Bs B's) 
    (S (max n m))

  | depth_coerces_sum : forall e A B A' B' s HsubA A's As s' HsubBB' Bs B's sum sum', 
    forall n m, depth HsubA n -> depth HsubBB' m ->
    @depth e (Sum A B) (Sum A' B') s' 
    (@coerces_sum e A B A' B' s HsubA A's As s' HsubBB' Bs B's sum sum')
    (S (max n m))

  | depth_coerces_sub_l : forall e U P U' HsubU Ps, 
    forall n, depth HsubU n ->
    @depth e (Subset U P) U' set (@coerces_sub_l e U P U' HsubU Ps) (S n)

  | depth_coerces_sub_r : forall e U U' P HsubU Ps,
    forall n, depth HsubU n ->
    @depth e U (Subset U' P) set (@coerces_sub_r e U U' P HsubU Ps) (S n)

  | depth_coerces_conv_l : forall e A B C s As Bs Cs convAB HsubBC,
    forall n, depth HsubBC n ->
    @depth e A C s (@coerces_conv_l e A B C s As Bs Cs convAB HsubBC) (S n)

  | depth_coerces_conv_r : forall e A B C s As Bs Cs HsubAB convBC, 
    forall n, depth HsubAB n ->
    @depth e A C s (@coerces_conv_r e A B C s As Bs Cs HsubAB convBC) (S n).

Hint Resolve depth_coerces_refl depth_coerces_prod depth_coerces_sum depth_coerces_sub_l depth_coerces_sub_r : coc.
Hint Resolve depth_coerces_conv_l depth_coerces_conv_r : coc.

Scheme depth_dep := Induction for depth Sort Prop.

Lemma depth_inj : forall e T U s, forall d : e |- T >>> U : s, exists n, depth d n.
Proof.
  intros e T U s d.
  induction d using coerces_db_dep ; auto with coc core.

  exists 0 ; auto with coc.

  destruct IHd1 as [n d1n] ; destruct IHd2 as [m d2m].
  exists (S (max n m)) ; auto with coc.

  destruct IHd1 as [n d1n] ; destruct IHd2 as [m d2m].
  exists (S (max n m)) ; auto with coc.

  destruct IHd as [n d1n].
  exists (S n) ; auto with coc.

  destruct IHd as [n d1n].
  exists (S n) ; auto with coc.

  destruct IHd as [n d1n].
  exists (S n) ; auto with coc.

  destruct IHd as [n d1n].
  exists (S n) ; auto with coc.
Save.

Derive Inversion_clear depth_inv with (forall (e : env) (A : term) (s : sort),
  forall H : (e |- A : Srt s), 
  forall n : nat, depth (coerces_refl H) n) Sort Prop.

Lemma depth_fun : forall e T U s, forall d : e |- T >>> U : s, 
  forall n n', depth d n -> depth d n' -> n = n'.
Proof.
  intros e T U s d.
  induction d using coerces_db_dep ; auto with coc core.
  intros.
  
  intros n n' d1 d2.
  induction d1; try induction d2 ; try discriminate.
  elim d2 ; intros ; auto with coc core.

  
  intros.
  
