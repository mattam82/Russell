Require Import Lambda.Terms.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Env.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

(** printing = $=$ *)
(** printing >> $\sub$ *)
(** printing |-= $\type$ *)

Reserved Notation "G |-= T = U : s" (at level 70, T, U, s at next level).
Reserved Notation "G |-= T >> U : s" (at level 70, T, U, s at next level).
Reserved Notation "G |-= T : U" (at level 70, T, U at next level).

Definition sum_sort s1 s2 s3 :=
  (s1 = set /\ s2 = set /\ s3 = set) \/
  (s1 = prop /\ s2 = prop /\ s3 = prop).

Inductive coerce : env -> term -> term -> sort -> Prop :=
  | coerce_conv : forall e A B s, e |-= A = B : Srt s -> e |-= A >> B : s
  
  | coerce_weak : forall e A B s, e |-= A >> B : s ->
  forall T s', e |-= T : Srt s' -> (T :: e) |-= lift 1 A >> lift 1 B : s

  | coerce_prod : forall e A B A' B',
  forall s, e |-= A' >> A : s ->
  (* derivable *) e |-= A' : Srt s -> e |-= A : Srt s ->
  forall s', (A' :: e) |-= B >> B' : s' -> 
  (* derivable *) A :: e |-= B : Srt s' -> A' :: e |-= B' : Srt s' ->
  e |-= (Prod A B) >> (Prod A' B') : s'
  
  | coerce_sum : forall e A B A' B',
  forall s, e |-= A >> A' : s -> 
  (* derivable *) e |-= A' : Srt s -> e |-= A : Srt s ->
  forall s', (A :: e) |-= B >> B' : s' ->
  (* derivable *) A :: e |-= B : Srt s' -> A' :: e |-= B' : Srt s' ->
  forall s'', sum_sort s s' s'' -> sum_sort s s' s'' ->
  e |-= (Sum A B) >> (Sum A' B') : s''

  | coerce_sub_l : forall e U P U', 	
  e |-= U >> U' : set ->
  (* derivable *) e |-= U : Srt set -> e |-= U' : Srt set ->
  (* derivable *) U :: e |-= P : Srt prop ->
  e |-= Subset U P >> U' : set

  | coerce_sub_r : forall e U U' P,
  e |-= U >> U' : set -> 
  (* derivable *) e |-= U : Srt set -> e |-= U' : Srt set ->
  (* derivable *) U' :: e |-= P : Srt prop ->
  e |-= U >> (Subset U' P) : set

  | coerce_sym : forall e U V s, e |-= U >> V : s -> e |-= V >> U : s

  | coerce_trans : forall e A B C s,  
  e |-= A >> B : s -> e |-= B >> C : s -> e |-= A >> C : s

where "G |-= T >> U : s" := (coerce G T U s)

with jeq : env -> term -> term -> term -> Prop :=
  | jeq_weak : forall e M N A, e |-= M = N : A ->
  forall B s, e |-= B : Srt s ->
  (B :: e) |-= lift 1 M = lift 1 N : lift 1 A

  | jeq_prod : forall e U V U' V' s1 s2, 
  e |-= U = U' : Srt s1 -> U :: e |-= V = V' : Srt s2 ->
  e |-= Prod U V = Prod U' V' : Srt s2

  | jeq_abs : forall e A A' s1, e |-= A = A' : Srt s1 ->
  forall B s2, (A :: e) |-= B : Srt s2 ->
  forall M M', (A :: e) |-= M = M' : B -> 
  e |-= Abs A M = Abs A' M' : (Prod A B)
  
  | jeq_app : forall e A B M M', e |-= M = M' : (Prod A B) -> 
  forall N N', e |-= N = N' : A ->
  e |-= App M N = App M' N' : subst N B

  | jeq_beta : forall e A s1, e |-= A : Srt s1 ->
  forall B s2, (A :: e) |-= B : Srt s2 ->
  forall M, (A :: e) |-= M : B -> 
  forall N, e |-= N : A ->
  e |-= App (Abs A M) N = subst N M : subst N B

  | jeq_sum : forall e A A' s1, e |-= A = A' : Srt s1 ->
  forall B B' s2, (A :: e) |-= B = B' : Srt s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  e |-= Sum A B = Sum A' B' : Srt s3
  
  | jeq_pair : forall e A A' s1, e |-= A = A' : Srt s1 ->
  forall B B' s2, (A :: e) |-= B = B' : Srt s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u u', e |-= u = u' : A ->
  forall v v', e |-= v = v' : subst u B ->
  e |-= Pair (Sum A B) u v = Pair (Sum A' B') u' v' : Sum A B

  | jeq_pi1 : forall e t t' A B, e |-= t = t' : Sum A B ->
  e |-= Pi1 t = Pi1 t' : A

  | jeq_pi1_red : forall e A s1, e |-= A : Srt s1 ->
  forall B s2, (A :: e) |-= B : Srt s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u, e |-= u : A -> forall v, e |-= v : subst u B ->
  e |-= Pi1 (Pair (Sum A B) u v) = u : A

  | jeq_pi2 : forall e t t' A B, e |-= t = t' : Sum A B ->
  e |-= Pi2 t = Pi2 t' : subst (Pi1 t) B

  | jeq_pi2_red : forall e A s1, e |-= A : Srt s1 ->
  forall B s2, (A :: e) |-= B : Srt s2 ->
  forall s3, sum_sort s1 s2 s3 ->
  forall u, e |-= u : A -> forall v, e |-= v : subst u B ->
  e |-= Pi2 (Pair (Sum A B) u v) = v : subst u B

  | jeq_subset : forall e A A', e |-= A = A' : Srt set ->
  forall B B', (A :: e) |-= B = B' : Srt prop ->
  e |-= Subset A B = Subset A' B' : Srt set

  | jeq_refl : forall e M A, e |-= M : A -> e |-= M = M : A
  
  | jeq_sym : forall e M N A, e |-= M = N : A -> e |-= N = M : A
  
  | jeq_trans : forall e M N P A, e |-= M = N : A -> e |-= N = P : A -> e |-= M =  P : A
  
  | jeq_conv : forall e M N A B s, e |-= M = N : A -> e |-= A >> B : s -> e |-= M = N : B

where "G |-= T = U : s" := (jeq G T U s)

with typ : env -> term -> term -> Prop :=
  | type_prop : nil |-= (Srt prop) : (Srt kind)
  | type_set : nil |-= (Srt set) : (Srt kind)	
  | type_var :
      forall e T s, e |-= T : Srt s -> (T :: e) |-= (Ref 0) : (lift 1 T)
  | type_weak :
      forall e t T, e |-= t : T -> forall U s, e |-= U : Srt s ->
      (U :: e) |-= lift 1 t : lift 1 T
  | type_abs :
      forall e T s1,
      e |-= T : (Srt s1) ->
      forall M (U : term) s2,
      (T :: e) |-= U : (Srt s2) ->
      (T :: e) |-= M : U -> 
      e |-= (Abs T M) : (Prod T U)
  | type_app :
      forall e v (V : term), e |-= v : V ->
      forall u (Ur : term), e |-= u : (Prod V Ur) -> 
      e |-= (App u v) : (subst v Ur)	

  | type_pair :
    forall e (U : term) s1, e |-= U : (Srt s1) ->
    forall u, e |-= u : U ->
    forall V s2, (U :: e) |-= V : (Srt s2) ->
    forall v, e |-= v : (subst u V) -> 
    forall s3, sum_sort s1 s2 s3 ->
    e |-= (Pair (Sum U V) u v) : (Sum U V)

  | type_prod :
      forall e T s1,
      e |-= T : (Srt s1) ->
      forall (U : term) s2,
      (T :: e) |-= U : (Srt s2) -> 
      e |-= (Prod T U) : (Srt s2)

  | type_sum :
      forall e T s1,
      e |-= T : (Srt s1) ->
      forall (U : term) s2,
      (T :: e) |-= U : (Srt s2) -> 
      forall s3, sum_sort s1 s2 s3 ->
      e |-= (Sum T U) : Srt s3

  | type_subset : 
      forall e T, e |-= T : (Srt set) ->
      forall (U : term), (T :: e) |-= U : (Srt prop) -> 
      e |-= (Subset T U) : (Srt set)

  | type_pi1 :
      forall e t U V, e |-= t : (Sum U V) -> 
      e |-= (Pi1 t) : U

  | type_pi2 :
      forall e t U V, e |-= t : (Sum U V) -> 
      e |-= (Pi2 t) : (subst (Pi1 t) V)

  | type_conv :
      forall e t (U V : term),
      e |-= t : U -> 
      forall s, e |-= U >> V : s -> 
      e |-= t : V

where "G |-= T : U" :=  (typ G T U).

(* begin hide *)
Hint Resolve coerce_conv coerce_weak coerce_sym coerce_prod coerce_sum coerce_sub_l coerce_sub_r coerce_trans : coc.
Hint Resolve jeq_refl jeq_sym jeq_beta : coc.
Hint Resolve type_pi1 type_pi2 type_pair type_prop type_set type_var type_weak: coc.
(* end hide *)

Inductive consistent : env -> Prop :=
 | consistent_nil : consistent nil
 | consistent_cons : forall e, consistent e ->
 forall T s, e |-= T : Srt s -> consistent (T :: e).

Hint Resolve consistent_nil consistent_cons : coc.

Scheme typ_dep := Induction for typ Sort Prop.

Scheme typ_coerce_mutind := Induction for typ Sort Prop
with coerce_typ_mutind := Induction for coerce Sort Prop.

Scheme typ_coerce_jeq_mutind := Induction for typ Sort Prop
with coerce_typ_jeq_mutind := Induction for coerce Sort Prop
with jeq_typ_coerce_mutind := Induction for jeq Sort Prop.

Combined Scheme typ_coerce_jeq_ind from typ_coerce_jeq_mutind, coerce_typ_jeq_mutind, jeq_typ_coerce_mutind.

