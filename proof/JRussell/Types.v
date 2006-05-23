Require Import Lambda.Terms.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Env.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Reserved Notation "G |- T = U : s" (at level 70, T, U, s at next level).
Reserved Notation "G |- T >> U : s" (at level 70, T, U, s at next level).
Reserved Notation "G |- T : U" (at level 70, T, U at next level).

Definition sum_sort s1 s2 s3 :=
  (s1 = set /\ s2 = set /\ s3 = set) \/
  (s1 = prop /\ s2 = prop /\ s3 = prop).

Inductive coerce : env -> term -> term -> sort -> Prop :=
  | coerce_conv : forall e A B s, e |- A = B : Srt s -> e |- A >> B : s
  
  | coerce_weak : forall e A B s, e |- A >> B : s ->
  forall T s', e |- T : Srt s' -> (T :: e) |- lift 1 A >> lift 1 B : s

  | coerce_prod : forall e A B A' B',
  forall s, e |- A' >> A : s ->
  (* derivable *) e |- A' : Srt s -> e |- A : Srt s ->
  forall s', (A' :: e) |- B >> B' : s' -> 
  (* derivable *) A :: e |- B : Srt s' -> A' :: e |- B' : Srt s' ->
  e |- (Prod A B) >> (Prod A' B') : s'
  
  | coerce_sum : forall e A B A' B',
  forall s, e |- A >> A' : s -> 
  (* derivable *) e |- A' : Srt s -> e |- A : Srt s ->
  forall s', (A :: e) |- B >> B' : s' ->
  (* derivable *) A :: e |- B : Srt s' -> A' :: e |- B' : Srt s' ->
  forall s'', sum_sort s s' s'' -> sum_sort s s' s'' ->
  e |- (Sum A B) >> (Sum A' B') : s''

  | coerce_sub_l : forall e U P U', 	
  e |- U >> U' : set ->
  (* derivable *) e |- U : Srt set -> e |- U' : Srt set ->
  (* derivable *) U :: e |- P : Srt prop ->
  e |- Subset U P >> U' : set

  | coerce_sub_r : forall e U U' P,
  e |- U >> U' : set -> 
  (* derivable *) e |- U : Srt set -> e |- U' : Srt set ->
  (* derivable *) U' :: e |- P : Srt prop ->
  e |- U >> (Subset U' P) : set

  | coerce_sym : forall e U V s, e |- U >> V : s -> e |- V >> U : s

  | coerce_trans : forall e A B C s,  
  e |- A >> B : s -> e |- B >> C : s -> e |- A >> C : s

where "G |- T >> U : s" := (coerce G T U s)

with jeq : env -> term -> term -> term -> Prop :=
  | jeq_weak : forall e M N A, e |- M = N : A ->
  forall B s, e |- B : Srt s ->
  (B :: e) |- lift 1 M = lift 1 N : lift 1 A

  | jeq_prod : forall e U V U' V' s1 s2, 
  e |- U = U' : Srt s1 -> U :: e |- V = V' : Srt s2 ->
  e |- Prod U V = Prod U' V' : Srt s2

  | jeq_abs : forall e A A' s1, e |- A = A' : Srt s1 ->
  forall B s2, (A :: e) |- B : Srt s2 ->
  forall M M', (A :: e) |- M = M' : B -> 
  e |- Abs A M = Abs A' M' : (Prod A B)
  
  | jeq_app : forall e A B M M', e |- M = M' : (Prod A B) -> 
  forall N N', e |- N = N' : A ->
  e |- App M N = App M' N' : subst N B

  | jeq_beta : forall e A s1, e |- A : Srt s1 ->
  forall B s2, (A :: e) |- B : Srt s2 ->
  forall M, (A :: e) |- M : B -> 
  forall N, e |- N : A ->
  e |- App (Abs A M) N = subst N M : subst N B

  | jeq_red : forall e M N A, e |- M = N : A -> 
  forall B s, e |- A = B : Srt s ->
  e |- M = N : B
  
  | jeq_exp : forall e M N B, e |- M = N : B -> 
  forall A s, e |- A = B : Srt s ->
  e |- M = N : A

  | jeq_sum : forall e A A' s1, e |- A = A' : Srt s1 ->
  forall B B' s2, (A :: e) |- B = B' : Srt s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  e |- Sum A B = Sum A' B' : Srt s3
  
  | jeq_pair : forall e A A' s1, e |- A = A' : Srt s1 ->
  forall B B' s2, (A :: e) |- B = B' : Srt s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u', e |- u = u' : A ->
  forall v v', e |- v = v' : subst u B ->
  e |- Pair (Sum A B) u v = Pair (Sum A' B') u' v' : Sum A B

  | jeq_pi1 : forall e t t' A B, e |- t = t' : Sum A B ->
  e |- Pi1 t = Pi1 t' : A

  | jeq_pi1_red : forall e A s1, e |- A : Srt s1 ->
  forall B s2, (A :: e) |- B : Srt s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u, e |- u : A -> forall v, e |- v : subst u B ->
  e |- Pi1 (Pair (Sum A B) u v) = u : A

  | jeq_pi2 : forall e t t' A B, e |- t = t' : Sum A B ->
  e |- Pi2 t = Pi2 t' : subst (Pi1 t) B

  | jeq_pi2_red : forall e A s1, e |- A : Srt s1 ->
  forall B s2, (A :: e) |- B : Srt s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u, e |- u : A -> forall v, e |- v : subst u B ->
  e |- Pi2 (Pair (Sum A B) u v) = v : subst u B

  | jeq_subset : forall e A A', e |- A = A' : Srt set ->
  forall B B', (A :: e) |- B = B' : Srt prop ->
  e |- Subset A B = Subset A' B' : Srt set

  | jeq_refl : forall e M A, e |- M : A -> e |- M = M : A
  
  | jeq_sym : forall e M N A, e |- M = N : A -> e |- N = M : A
  
  | jeq_trans : forall e M N P A, e |- M = N : A -> e |- N = P : A -> e |- M =  P : A
  
  | jeq_conv : forall e M N A B s, e |- M = N : A -> e |- A >> B : s -> e |- M = N : B

where "G |- T = U : s" := (jeq G T U s)

with typ : env -> term -> term -> Prop :=
  | type_prop : nil |- (Srt prop) : (Srt kind)
  | type_set : nil |- (Srt set) : (Srt kind)	
  | type_var :
      forall e T s, e |- T : Srt s -> (T :: e) |- (Ref 0) : (lift 1 T)
  | type_weak :
      forall e t T, e |- t : T -> forall U s, e |- U : Srt s ->
      (U :: e) |- lift 1 t : lift 1 T
  | type_abs :
      forall e T s1,
      e |- T : (Srt s1) ->
      forall M (U : term) s2,
      (T :: e) |- U : (Srt s2) ->
      (T :: e) |- M : U -> 
      e |- (Abs T M) : (Prod T U)
  | type_app :
      forall e v (V : term), e |- v : V ->
      forall u (Ur : term), e |- u : (Prod V Ur) -> 
      e |- (App u v) : (subst v Ur)	

  | type_pair :
    forall e (U : term) s1, e |- U : (Srt s1) ->
    forall u, e |- u : U ->
    forall V s2, (U :: e) |- V : (Srt s2) ->
    forall v, e |- v : (subst u V) -> 
    forall s3, sum_sort s1 s2 s3 ->
    e |- (Pair (Sum U V) u v) : (Sum U V)

  | type_prod :
      forall e T s1,
      e |- T : (Srt s1) ->
      forall (U : term) s2,
      (T :: e) |- U : (Srt s2) -> 
      e |- (Prod T U) : (Srt s2)

  | type_sum :
      forall e T s1,
      e |- T : (Srt s1) ->
      forall (U : term) s2,
      (T :: e) |- U : (Srt s2) -> 
      forall s3, sum_sort s1 s2 s3 ->
      e |- (Sum T U) : Srt s3

  | type_subset : 
      forall e T, e |- T : (Srt set) ->
      forall (U : term), (T :: e) |- U : (Srt prop) -> 
      e |- (Subset T U) : (Srt set)

  | type_pi1 :
      forall e t U V, e |- t : (Sum U V) -> 
      e |- (Pi1 t) : U

  | type_pi2 :
      forall e t U V, e |- t : (Sum U V) -> 
      e |- (Pi2 t) : (subst (Pi1 t) V)

  | type_conv :
      forall e t (U V : term),
      e |- t : U -> 
      forall s, e |- U >> V : s -> 
      e |- t : V

where "G |- T : U" :=  (typ G T U).

Hint Resolve coerce_conv coerce_weak coerce_sym coerce_prod coerce_sum coerce_sub_l coerce_sub_r coerce_trans : coc.
Hint Resolve jeq_refl jeq_sym jeq_beta : coc.
Hint Resolve type_pi1 type_pi2 type_pair type_prop type_set type_var type_weak: coc.

Inductive consistent : env -> Prop :=
 | consistent_nil : consistent nil
 | consistent_cons : forall e, consistent e ->
 forall T s, e |- T : Srt s -> consistent (T :: e).

Hint Resolve consistent_nil consistent_cons : coc.

Scheme typ_dep := Induction for typ Sort Prop.

Scheme typ_coerce_jeq_mutind := Induction for typ Sort Prop
with coerce_typ_jeq_mutind := Induction for coerce Sort Prop
with jeq_typ_coerce_mutind := Induction for jeq Sort Prop.

Check typ_coerce_jeq_mutind.

Lemma typ_coerce_jeq_ind :
forall (P : forall (e : env) t t0, e |- t : t0 -> Prop)
         (P0 : forall (e : env) t t0 s, e |- t >> t0 : s -> Prop)
         (P1 : forall (e : env) t t0 t1, e |- t = t0 : t1 -> Prop),
       P nil (Srt prop) (Srt kind) type_prop ->
       P nil (Srt set) (Srt kind) type_set ->
       (forall (e : env) T s (t : e |- T : Srt s),
        P e T (Srt s) t -> P (T :: e) (Ref 0) (lift 1 T) (type_var t)) ->
       (forall (e : env) t T (t0 : e |- t : T),
        P e t T t0 ->
        forall (U : term) s (t1 : e |- U : Srt s),
        P e U (Srt s) t1 ->
        P (U :: e) (lift 1 t) (lift 1 T) (type_weak t0 t1)) ->
       (forall (e : env) T s1 (t : e |- T : Srt s1),
        P e T (Srt s1) t ->
        forall M (U : term) s2 (t0 : T :: e |- U : Srt s2),
        P (T :: e) U (Srt s2) t0 ->
        forall t1 : T :: e |- M : U,
        P (T :: e) M U t1 -> P e (Abs T M) (Prod T U) (type_abs t t0 t1)) ->
       (forall (e : env) v (V : term) (t : e |- v : V),
        P e v V t ->
        forall u (Ur : term) (t0 : e |- u : Prod V Ur),
        P e u (Prod V Ur) t0 -> P e (App u v) (subst v Ur) (type_app t t0)) ->
       (forall (e : env) (U : term) s1 (t : e |- U : Srt s1),
        P e U (Srt s1) t ->
        forall u (t0 : e |- u : U),
        P e u U t0 ->
        forall (V : term) s2 (t1 : U :: e |- V : Srt s2),
        P (U :: e) V (Srt s2) t1 ->
        forall v (t2 : e |- v : subst u V),
        P e v (subst u V) t2 ->
        forall s3 (s : sum_sort s1 s2 s3),
        P e (Pair (Sum U V) u v) (Sum U V) (type_pair t t0 t1 t2 s)) ->
       (forall (e : env) T s1 (t : e |- T : Srt s1),
        P e T (Srt s1) t ->
        forall (U : term) s2 (t0 : T :: e |- U : Srt s2),
        P (T :: e) U (Srt s2) t0 -> P e (Prod T U) (Srt s2) (type_prod t t0)) ->
       (forall (e : env) T s1 (t : e |- T : Srt s1),
        P e T (Srt s1) t ->
        forall (U : term) s2 (t0 : T :: e |- U : Srt s2),
        P (T :: e) U (Srt s2) t0 ->
        forall s3 (s : sum_sort s1 s2 s3),
        P e (Sum T U) (Srt s3) (type_sum t t0 s)) ->
       (forall (e : env) T (t : e |- T : Srt set),
        P e T (Srt set) t ->
        forall (U : term) (t0 : T :: e |- U : Srt prop),
        P (T :: e) U (Srt prop) t0 ->
        P e (Subset T U) (Srt set) (type_subset t t0)) ->
       (forall (e : env) t (U V : term) (t0 : e |- t : Sum U V),
        P e t (Sum U V) t0 -> P e (Pi1 t) U (type_pi1 t0)) ->
       (forall (e : env) t (U V : term) (t0 : e |- t : Sum U V),
        P e t (Sum U V) t0 -> P e (Pi2 t) (subst (Pi1 t) V) (type_pi2 t0)) ->
       (forall (e : env) t (U V : term) (t0 : e |- t : U),
        P e t U t0 ->
        forall s (c : e |- U >> V : s),
        P0 e U V s c -> P e t V (type_conv t0 c)) ->
       (forall (e : env) A B s (j : e |- A = B : Srt s),
        P1 e A B (Srt s) j -> P0 e A B s (coerce_conv j)) ->
       (forall (e : env) A B s (c : e |- A >> B : s),
        P0 e A B s c ->
        forall T s' (t : e |- T : Srt s'),
        P e T (Srt s') t ->
        P0 (T :: e) (lift 1 A) (lift 1 B) s (coerce_weak c t)) ->
       (forall (e : env) A B A' B' s (c : e |- A' >> A : s),
        P0 e A' A s c ->
        forall t : e |- A' : Srt s,
        P e A' (Srt s) t ->
        forall t0 : e |- A : Srt s,
        P e A (Srt s) t0 ->
        forall s' (c0 : A' :: e |- B >> B' : s'),
        P0 (A' :: e) B B' s' c0 ->
        forall t1 : A :: e |- B : Srt s',
        P (A :: e) B (Srt s') t1 ->
        forall t2 : A' :: e |- B' : Srt s',
        P (A' :: e) B' (Srt s') t2 ->
        P0 e (Prod A B) (Prod A' B') s' (coerce_prod c t t0 c0 t1 t2)) ->
       (forall (e : env) A B A' B' s (c : e |- A >> A' : s),
        P0 e A A' s c ->
        forall t : e |- A' : Srt s,
        P e A' (Srt s) t ->
        forall t0 : e |- A : Srt s,
        P e A (Srt s) t0 ->
        forall s' (c0 : A :: e |- B >> B' : s'),
        P0 (A :: e) B B' s' c0 ->
        forall t1 : A :: e |- B : Srt s',
        P (A :: e) B (Srt s') t1 ->
        forall t2 : A' :: e |- B' : Srt s',
        P (A' :: e) B' (Srt s') t2 ->
        forall s'' (s0 s1 : sum_sort s s' s''),
        P0 e (Sum A B) (Sum A' B') s'' (coerce_sum c t t0 c0 t1 t2 s0 s1)) ->
       (forall (e : env) (U P2 U' : term) (c : e |- U >> U' : set),
        P0 e U U' set c ->
        forall t : e |- U : Srt set,
        P e U (Srt set) t ->
        forall t0 : e |- U' : Srt set,
        P e U' (Srt set) t0 ->
        forall t1 : U :: e |- P2 : Srt prop,
        P (U :: e) P2 (Srt prop) t1 ->
        P0 e (Subset U P2) U' set (coerce_sub_l c t t0 t1)) ->
       (forall (e : env) (U U' P2 : term) (c : e |- U >> U' : set),
        P0 e U U' set c ->
        forall t : e |- U : Srt set,
        P e U (Srt set) t ->
        forall t0 : e |- U' : Srt set,
        P e U' (Srt set) t0 ->
        forall t1 : U' :: e |- P2 : Srt prop,
        P (U' :: e) P2 (Srt prop) t1 ->
        P0 e U (Subset U' P2) set (coerce_sub_r c t t0 t1)) ->
       (forall (e : env) (U V : term) s (c : e |- U >> V : s),
        P0 e U V s c -> P0 e V U s (coerce_sym c)) ->
       (forall (e : env) A B (C : term) s (c : e |- A >> B : s),
        P0 e A B s c ->
        forall c0 : e |- B >> C : s,
        P0 e B C s c0 -> P0 e A C s (coerce_trans c c0)) ->
       (forall (e : env) M N A (j : e |- M = N : A),
        P1 e M N A j ->
        forall B s (t : e |- B : Srt s),
        P e B (Srt s) t ->
        P1 (B :: e) (lift 1 M) (lift 1 N) (lift 1 A) (jeq_weak j t)) ->
       (forall (e : env) (U V U' V' : term) s1 s2 (j : e |- U = U' : Srt s1),
        P1 e U U' (Srt s1) j ->
        forall j0 : U :: e |- V = V' : Srt s2,
        P1 (U :: e) V V' (Srt s2) j0 ->
        P1 e (Prod U V) (Prod U' V') (Srt s2) (jeq_prod j j0)) ->
       (forall (e : env) A A' s1 (j : e |- A = A' : Srt s1),
        P1 e A A' (Srt s1) j ->
        forall B s2 (t : A :: e |- B : Srt s2),
        P (A :: e) B (Srt s2) t ->
        forall M M' (j0 : A :: e |- M = M' : B),
        P1 (A :: e) M M' B j0 ->
        P1 e (Abs A M) (Abs A' M') (Prod A B) (jeq_abs j t j0)) ->
       (forall (e : env) A B M M' (j : e |- M = M' : Prod A B),
        P1 e M M' (Prod A B) j ->
        forall N N' (j0 : e |- N = N' : A),
        P1 e N N' A j0 ->
        P1 e (App M N) (App M' N') (subst N B) (jeq_app j j0)) ->
       (forall (e : env) A s1 (t : e |- A : Srt s1),
        P e A (Srt s1) t ->
        forall B s2 (t0 : A :: e |- B : Srt s2),
        P (A :: e) B (Srt s2) t0 ->
        forall M (t1 : A :: e |- M : B),
        P (A :: e) M B t1 ->
        forall N (t2 : e |- N : A),
        P e N A t2 ->
        P1 e (App (Abs A M) N) (subst N M) (subst N B) (jeq_beta t t0 t1 t2)) ->
       (forall (e : env) M N A (j : e |- M = N : A),
        P1 e M N A j ->
        forall B s (j0 : e |- A = B : Srt s),
        P1 e A B (Srt s) j0 -> P1 e M N B (jeq_red j j0)) ->
       (forall (e : env) M N B (j : e |- M = N : B),
        P1 e M N B j ->
        forall A s (j0 : e |- A = B : Srt s),
        P1 e A B (Srt s) j0 -> P1 e M N A (jeq_exp j j0)) ->
       (forall (e : env) A A' s1 (j : e |- A = A' : Srt s1),
        P1 e A A' (Srt s1) j ->
        forall B B' s2 (j0 : A :: e |- B = B' : Srt s2),
        P1 (A :: e) B B' (Srt s2) j0 ->
        forall s3 (s : sum_sort s1 s2 s3),
        P1 e (Sum A B) (Sum A' B') (Srt s3) (jeq_sum j j0 s)) ->
       (forall (e : env) A A' s1 (j : e |- A = A' : Srt s1),
        P1 e A A' (Srt s1) j ->
        forall B B' s2 (j0 : A :: e |- B = B' : Srt s2),
        P1 (A :: e) B B' (Srt s2) j0 ->
        forall s3 (s : sum_sort s1 s2 s3) u u' (j1 : e |- u = u' : A),
        P1 e u u' A j1 ->
        forall v v' (j2 : e |- v = v' : subst u B),
        P1 e v v' (subst u B) j2 ->
        P1 e (Pair (Sum A B) u v) (Pair (Sum A' B') u' v') (Sum A B)
          (jeq_pair j j0 s j1 j2)) ->
       (forall (e : env) t t' A B (j : e |- t = t' : Sum A B),
        P1 e t t' (Sum A B) j -> P1 e (Pi1 t) (Pi1 t') A (jeq_pi1 j)) ->
       (forall (e : env) A s1 (t : e |- A : Srt s1),
        P e A (Srt s1) t ->
        forall B s2 (t0 : A :: e |- B : Srt s2),
        P (A :: e) B (Srt s2) t0 ->
        forall s3 (s : sum_sort s1 s2 s3) u (t1 : e |- u : A),
        P e u A t1 ->
        forall v (t2 : e |- v : subst u B),
        P e v (subst u B) t2 ->
        P1 e (Pi1 (Pair (Sum A B) u v)) u A (jeq_pi1_red t t0 s t1 t2)) ->
       (forall (e : env) t t' A B (j : e |- t = t' : Sum A B),
        P1 e t t' (Sum A B) j ->
        P1 e (Pi2 t) (Pi2 t') (subst (Pi1 t) B) (jeq_pi2 j)) ->
       (forall (e : env) A s1 (t : e |- A : Srt s1),
        P e A (Srt s1) t ->
        forall B s2 (t0 : A :: e |- B : Srt s2),
        P (A :: e) B (Srt s2) t0 ->
        forall s3 (s : sum_sort s1 s2 s3) u (t1 : e |- u : A),
        P e u A t1 ->
        forall v (t2 : e |- v : subst u B),
        P e v (subst u B) t2 ->
        P1 e (Pi2 (Pair (Sum A B) u v)) v (subst u B) (jeq_pi2_red t t0 s t1 t2)) ->
       (forall (e : env) A A' (j : e |- A = A' : Srt set),
        P1 e A A' (Srt set) j ->
        forall B B' (j0 : A :: e |- B = B' : Srt prop),
        P1 (A :: e) B B' (Srt prop) j0 ->
        P1 e (Subset A B) (Subset A' B') (Srt set) (jeq_subset j j0)) ->
       (forall (e : env) M A (t : e |- M : A),
        P e M A t -> P1 e M M A (jeq_refl t)) ->
       (forall (e : env) M N A (j : e |- M = N : A),
        P1 e M N A j -> P1 e N M A (jeq_sym j)) ->
       (forall (e : env) M N (P2 : term) A (j : e |- M = N : A),
        P1 e M N A j ->
        forall j0 : e |- N = P2 : A,
        P1 e N P2 A j0 -> P1 e M P2 A (jeq_trans j j0)) ->
       (forall (e : env) M N A B s (j : e |- M = N : A),
        P1 e M N A j ->
        forall c : e |- A >> B : s, P0 e A B s c -> P1 e M N B (jeq_conv j c)) ->


       (forall (e : env) t t0 (c : e |- t : t0 ), P e t t0 c)
       /\ (forall (e : env) t t0 s (c : e |- t >> t0 : s), P0 e t t0 s c)
       /\ (forall (e : env) t t0 T (c : e |- t = t0 : T), P1 e t t0 T c).
Proof.
  intros.
  split.
  intros ; eapply typ_coerce_jeq_mutind with (P:=P) (P0:=P0) (P1:=P1) ; auto ; auto.
  split ; intros.
  eapply coerce_typ_jeq_mutind with (P:=P) (P0:=P0) (P1:=P1) ; auto ; auto.
  eapply jeq_typ_coerce_mutind with (P:=P) (P0:=P0) (P1:=P1) ; auto ; auto.
Qed.

