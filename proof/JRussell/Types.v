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
  | coerce_refl : forall e A s, e |- A : Srt s -> e |- A >> A : s

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

  | coerce_conv : forall e A B C D s,  
  e |- A = B : Srt s -> e |- B >> C : s -> e |- C = D : Srt s -> e |- A >> D : s

where "G |- T >> U : s" := (coerce G T U s)

with jeq : env -> term -> term -> term -> Prop :=
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
  
  | jeq_pi1 : forall e A A' s1, e |- A = A' : Srt s1 ->
  forall B B' s2, (A :: e) |- B = B' : Srt s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |- t = t' : Sum A B ->
  e |- Pi1 t = Pi1 t' : A

  | jeq_pi1_red : forall e A A' s1, e |- A = A' : Srt s1 ->
  forall B B' s2, (A :: e) |- B = B' : Srt s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', e |- Pair (Sum A B) u v = Pair (Sum A' B') u' v' : Sum A B ->
  e |- Pi1 (Pair (Sum A B) u v) = u : A

  | jeq_pi2 : forall e A A' s1, e |- A = A' : Srt s1 ->
  forall B B' s2, (A :: e) |- B = B' : Srt s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall t t', e |- t = t' : Sum A B ->
  e |- Pi2 t = Pi2 t' : subst (Pi1 t) B

  | jeq_pi2_red : forall e A A' s1, e |- A = A' : Srt s1 ->
  forall B B' s2, (A :: e) |- B = B' : Srt s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u' v v', 
  e |- Pair (Sum A B) u v = Pair (Sum A' B') u' v' : Sum A B ->
  e |- Pi2 (Pair (Sum A B) u v) = v : subst u B

  | jeq_subset : forall e A A', e |- A = A' : Srt set ->
  forall B B', (A :: e) |- B = B' : Srt prop ->
  e |- Subset A B = Subset A' B' : Srt set

  | jeq_refl : forall e M A, e |- M : A -> e |- M = M : A
  
  | jeq_sym : forall e M N A, e |- M = N : A -> e |- N = M : A
  
  | jeq_trans : forall e M N P A, e |- M = N : A -> e |- N = P : A -> e |- M =  P : A
  
  | jeq_conv : forall e M N A B s, e |- M = N : A -> e |- A = B : Srt s -> e |- M = N : B

where "G |- T = U : s" := (jeq G T U s)

with wf : env -> Prop :=
  | wf_nil : wf nil
  | wf_var : forall e T s, e |- T : (Srt s) -> wf (T :: e)

with typ : env -> term -> term -> Prop :=
  | type_prop : forall e, wf e -> e |- (Srt prop) : (Srt kind)
  | type_set : forall e, wf e -> e |- (Srt set) : (Srt kind)	
  | type_var : (* start *)
      forall e, wf e -> forall n T, item_lift T e n -> e |- (Ref n) : T
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

Hint Resolve coerce_refl coerce_conv coerce_prod coerce_sum coerce_sub_l coerce_sub_r : coc.
Hint Resolve jeq_refl jeq_sym jeq_beta : coc.
Hint Resolve type_pi1 type_pi2 type_pair type_prop type_set type_var: coc.

Scheme typ_dep := Induction for typ Sort Prop.

Scheme typ_wf_mut := Induction for typ Sort Prop
with wf_typ_mut := Induction for wf Sort Prop.

Scheme typ_coerce_jeq_mutind := Induction for typ Sort Prop
with coerce_typ_jeq_mutind := Induction for coerce Sort Prop
with jeq_typ_coerce_mutind := Induction for jeq Sort Prop.

Scheme typ_coerce_wf_jeq_mutind := Induction for typ Sort Prop
with coerce_typ_wf_jeq_mutind := Induction for coerce Sort Prop
with jeq_typ_wf_coerce_mutind := Induction for jeq Sort Prop
with wf_typ_coerce_jeq_mutind := Induction for wf Sort Prop.

Check typ_coerce_jeq_mutind.

Lemma typ_coerce_jeq_ind :
forall (P : forall (e : env) t t0, e |- t : t0 -> Prop)
         (P0 : forall (e : env) t t0 s, e |- t >> t0 : s -> Prop)
         (P1 : forall (e : env) t t0 t1, e |- t = t0 : t1 -> Prop),
       (forall (e : env) (w : wf e), P e (Srt prop) (Srt kind) (type_prop w)) ->
       (forall (e : env) (w : wf e), P e (Srt set) (Srt kind) (type_set w)) ->
       (forall (e : env) (w : wf e) n T (i : item_lift T e n),
        P e (Ref n) T (type_var w i)) ->
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
       (forall (e : env) A s (t : e |- A : Srt s),
        P e A (Srt s) t -> P0 e A A s (coerce_refl t)) ->
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
       (forall (e : env) A B (C D : term) s (j : e |- A = B : Srt s),
        P1 e A B (Srt s) j ->
        forall c : e |- B >> C : s,
        P0 e B C s c ->
        forall j0 : e |- C = D : Srt s,
        P1 e C D (Srt s) j0 -> P0 e A D s (coerce_conv j c j0)) ->
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
        forall s3 (s : sum_sort s1 s2 s3) t t' (j1 : e |- t = t' : Sum A B),
        P1 e t t' (Sum A B) j1 -> P1 e (Pi1 t) (Pi1 t') A (jeq_pi1 j j0 s j1)) ->
       (forall (e : env) A A' s1 (j : e |- A = A' : Srt s1),
        P1 e A A' (Srt s1) j ->
        forall B B' s2 (j0 : A :: e |- B = B' : Srt s2),
        P1 (A :: e) B B' (Srt s2) j0 ->
        forall s3 (s : sum_sort s1 s2 s3) u u' v v'
          (j1 : e |- Pair (Sum A B) u v = Pair (Sum A' B') u' v' : Sum A B),
        P1 e (Pair (Sum A B) u v) (Pair (Sum A' B') u' v') (Sum A B) j1 ->
        P1 e (Pi1 (Pair (Sum A B) u v)) u A (jeq_pi1_red j j0 s j1)) ->
       (forall (e : env) A A' s1 (j : e |- A = A' : Srt s1),
        P1 e A A' (Srt s1) j ->
        forall B B' s2 (j0 : A :: e |- B = B' : Srt s2),
        P1 (A :: e) B B' (Srt s2) j0 ->
        forall s3 (s : sum_sort s1 s2 s3) t t' (j1 : e |- t = t' : Sum A B),
        P1 e t t' (Sum A B) j1 ->
        P1 e (Pi2 t) (Pi2 t') (subst (Pi1 t) B) (jeq_pi2 j j0 s j1)) ->
       (forall (e : env) A A' s1 (j : e |- A = A' : Srt s1),
        P1 e A A' (Srt s1) j ->
        forall B B' s2 (j0 : A :: e |- B = B' : Srt s2),
        P1 (A :: e) B B' (Srt s2) j0 ->
        forall s3 (s : sum_sort s1 s2 s3) u u' v v'
          (j1 : e |- Pair (Sum A B) u v = Pair (Sum A' B') u' v' : Sum A B),
        P1 e (Pair (Sum A B) u v) (Pair (Sum A' B') u' v') (Sum A B) j1 ->
        P1 e (Pi2 (Pair (Sum A B) u v)) v (subst u B) (jeq_pi2_red j j0 s j1)) ->
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
        forall j0 : e |- A = B : Srt s,
        P1 e A B (Srt s) j0 -> P1 e M N B (jeq_conv j j0)) ->
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

Check (typ_coerce_wf_jeq_mutind).

Lemma typ_coerce_jeq_wf_ind :
forall (P : forall (e : env) t t0, e |- t : t0 -> Prop)
         (P0 : forall (e : env) t t0 s, e |- t >> t0 : s -> Prop)
         (P1 : forall (e : env) t t0 t1, e |- t = t0 : t1 -> Prop)
         (P2 : forall e : env, wf e -> Prop),
       (forall (e : env) (w : wf e),
        P2 e w -> P e (Srt prop) (Srt kind) (type_prop w)) ->
       (forall (e : env) (w : wf e),
        P2 e w -> P e (Srt set) (Srt kind) (type_set w)) ->
       (forall (e : env) (w : wf e),
        P2 e w ->
        forall n T (i : item_lift T e n), P e (Ref n) T (type_var w i)) ->
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
       (forall (e : env) A s (t : e |- A : Srt s),
        P e A (Srt s) t -> P0 e A A s (coerce_refl t)) ->
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
       (forall (e : env) (U P3 U' : term) (c : e |- U >> U' : set),
        P0 e U U' set c ->
        forall t : e |- U : Srt set,
        P e U (Srt set) t ->
        forall t0 : e |- U' : Srt set,
        P e U' (Srt set) t0 ->
        forall t1 : U :: e |- P3 : Srt prop,
        P (U :: e) P3 (Srt prop) t1 ->
        P0 e (Subset U P3) U' set (coerce_sub_l c t t0 t1)) ->
       (forall (e : env) (U U' P3 : term) (c : e |- U >> U' : set),
        P0 e U U' set c ->
        forall t : e |- U : Srt set,
        P e U (Srt set) t ->
        forall t0 : e |- U' : Srt set,
        P e U' (Srt set) t0 ->
        forall t1 : U' :: e |- P3 : Srt prop,
        P (U' :: e) P3 (Srt prop) t1 ->
        P0 e U (Subset U' P3) set (coerce_sub_r c t t0 t1)) ->
       (forall (e : env) A B (C D : term) s (j : e |- A = B : Srt s),
        P1 e A B (Srt s) j ->
        forall c : e |- B >> C : s,
        P0 e B C s c ->
        forall j0 : e |- C = D : Srt s,
        P1 e C D (Srt s) j0 -> P0 e A D s (coerce_conv j c j0)) ->
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
        forall s3 (s : sum_sort s1 s2 s3) t t' (j1 : e |- t = t' : Sum A B),
        P1 e t t' (Sum A B) j1 -> P1 e (Pi1 t) (Pi1 t') A (jeq_pi1 j j0 s j1)) ->
       (forall (e : env) A A' s1 (j : e |- A = A' : Srt s1),
        P1 e A A' (Srt s1) j ->
        forall B B' s2 (j0 : A :: e |- B = B' : Srt s2),
        P1 (A :: e) B B' (Srt s2) j0 ->
        forall s3 (s : sum_sort s1 s2 s3) u u' v v'
          (j1 : e |- Pair (Sum A B) u v = Pair (Sum A' B') u' v' : Sum A B),
        P1 e (Pair (Sum A B) u v) (Pair (Sum A' B') u' v') (Sum A B) j1 ->
        P1 e (Pi1 (Pair (Sum A B) u v)) u A (jeq_pi1_red j j0 s j1)) ->
       (forall (e : env) A A' s1 (j : e |- A = A' : Srt s1),
        P1 e A A' (Srt s1) j ->
        forall B B' s2 (j0 : A :: e |- B = B' : Srt s2),
        P1 (A :: e) B B' (Srt s2) j0 ->
        forall s3 (s : sum_sort s1 s2 s3) t t' (j1 : e |- t = t' : Sum A B),
        P1 e t t' (Sum A B) j1 ->
        P1 e (Pi2 t) (Pi2 t') (subst (Pi1 t) B) (jeq_pi2 j j0 s j1)) ->
       (forall (e : env) A A' s1 (j : e |- A = A' : Srt s1),
        P1 e A A' (Srt s1) j ->
        forall B B' s2 (j0 : A :: e |- B = B' : Srt s2),
        P1 (A :: e) B B' (Srt s2) j0 ->
        forall s3 (s : sum_sort s1 s2 s3) u u' v v'
          (j1 : e |- Pair (Sum A B) u v = Pair (Sum A' B') u' v' : Sum A B),
        P1 e (Pair (Sum A B) u v) (Pair (Sum A' B') u' v') (Sum A B) j1 ->
        P1 e (Pi2 (Pair (Sum A B) u v)) v (subst u B) (jeq_pi2_red j j0 s j1)) ->
       (forall (e : env) A A' (j : e |- A = A' : Srt set),
        P1 e A A' (Srt set) j ->
        forall B B' (j0 : A :: e |- B = B' : Srt prop),
        P1 (A :: e) B B' (Srt prop) j0 ->
        P1 e (Subset A B) (Subset A' B') (Srt set) (jeq_subset j j0)) ->
       (forall (e : env) M A (t : e |- M : A),
        P e M A t -> P1 e M M A (jeq_refl t)) ->
       (forall (e : env) M N A (j : e |- M = N : A),
        P1 e M N A j -> P1 e N M A (jeq_sym j)) ->
       (forall (e : env) M N (P3 : term) A (j : e |- M = N : A),
        P1 e M N A j ->
        forall j0 : e |- N = P3 : A,
        P1 e N P3 A j0 -> P1 e M P3 A (jeq_trans j j0)) ->
       (forall (e : env) M N A B s (j : e |- M = N : A),
        P1 e M N A j ->
        forall j0 : e |- A = B : Srt s,
        P1 e A B (Srt s) j0 -> P1 e M N B (jeq_conv j j0)) ->
       P2 nil wf_nil ->
       (forall (e : env) T s (t : e |- T : Srt s),
        P e T (Srt s) t -> P2 (T :: e) (wf_var t)) ->
       (forall (e : env) t t0 (c : e |- t : t0 ), P e t t0 c)
       /\ (forall (e : env) t t0 s (c : e |- t >> t0 : s), P0 e t t0 s c)
       /\ (forall (e : env) t t0 T (c : e |- t = t0 : T), P1 e t t0 T c)
       /\ (forall (e : env) (t1 : wf e), P2 e t1).
Proof.
  intros.
  split.
  intros ; eapply typ_coerce_wf_jeq_mutind with (P:=P) (P0:=P0) (P1:=P1) (P2:=P2) ; auto ; auto.
  split ; intros.
  eapply coerce_typ_wf_jeq_mutind with (P:=P) (P0:=P0) (P1 := P1) (P2:=P2) ; auto ; auto.
  split ; intros.
  eapply jeq_typ_wf_coerce_mutind with (P:=P) (P0:=P0) (P1 := P1) (P2:=P2) ; auto ; auto.
  eapply wf_typ_coerce_jeq_mutind with (P:=P) (P0:=P0) (P1 := P1) (P2:=P2) ; auto ; auto.
Qed.
  
  Lemma type_prop_set :
   forall s, is_prop s -> forall e, wf e -> typ e (Srt s) (Srt kind).
simple destruct 1; intros ; rewrite H0.
apply type_prop; trivial.
apply type_set; trivial.
Qed.


Lemma typ_free_db : forall e t T, typ e t T -> free_db (length e) t.
Proof.
  simple induction 1 ; intros ; auto with coc core arith datatypes.
  inversion_clear H1.
  apply db_ref.
  elim H3; simpl in |- *; intros; auto with coc core arith datatypes.
Qed.


Lemma typ_wf : forall e t T, e |- t : T -> wf e.
simple induction 1; auto with coc core arith datatypes.
Qed.


  Lemma wf_sort :
   forall n e f,
   trunc _ (S n) e f ->
   wf e -> forall t, item _ t e n -> exists s : sort, f |- t : (Srt s).
simple induction n.
do 3 intro.
inversion_clear H.
inversion_clear H0.
intros.
inversion_clear H0.
inversion_clear H.
exists s; auto with coc core arith datatypes.

do 5 intro.
inversion_clear H0.
intros.
inversion_clear H2.
inversion_clear H0.
elim H with e0 f t; intros; auto with coc core arith datatypes.
exists x0; auto with coc core arith datatypes.

apply typ_wf with x (Srt s); auto with coc core arith datatypes.
Qed.

Lemma left_not_kind : forall G t T, G |- t : T -> t <> Srt kind.
Proof.
  induction 1 ; intros ; unfold not ; intros ; try discriminate ; auto with coc.
Qed.

Lemma coerce_prop_prop : forall e, wf e -> e |- Srt prop >> Srt prop : kind.
Proof.
  intros.
  auto with coc.
Qed.

Lemma coerce_set_set : forall e, wf e -> e |- Srt set >> Srt set : kind.
Proof.
  intros.
  auto with coc.
Qed.

Lemma coerce_is_prop : forall e, wf e -> forall s, is_prop s -> e |- Srt s >> Srt s : kind.
Proof.
  intros.
  induction H0 ;
  rewrite H0 ; auto with coc.
Qed.

Lemma conv_coerce : forall e T T' s, e |- T' : Srt s -> e |- T = T' : Srt s ->
  e |- T >> T' : s.
Proof.
 intros.
 apply coerce_conv with T' T' ; auto with coc.
Qed.

Hint Resolve coerce_prop_prop coerce_set_set coerce_is_prop : coc.
Hint Resolve conv_coerce typ_wf left_not_kind : coc.
