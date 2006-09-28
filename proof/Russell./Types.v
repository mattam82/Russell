Require Import Lambda.Terms.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Env.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Reserved Notation "G |.- T = U : s" (at level 70, T, U, s at next level).
Reserved Notation "G |.- T >> U : s" (at level 70, T, U, s at next level).
Reserved Notation "G |.- T : U" (at level 70, T, U at next level).

Definition sum_sort s1 s2 s3 :=
  (s1 = set /\ s2 = set /\ s3 = set) \/
  (s1 = prop /\ s2 = prop /\ s3 = prop).

Inductive coerce : env -> term -> term -> sort -> Prop :=
  | coerce_refl : forall e A s, e |.- A : Srt s -> e |.- A >> A : s

  | coerce_prod : forall e A B A' B',
  forall s, e |.- A' >> A : s ->
  (* derivable *) e |.- A' : Srt s -> e |.- A : Srt s ->
  forall s', (A' :: e) |.- B >> B' : s' -> 
  (* derivable *) A :: e |.- B : Srt s' -> A' :: e |.- B' : Srt s' ->
  e |.- (Prod A B) >> (Prod A' B') : s'
  
  | coerce_sum : forall e A B A' B',
  forall s, e |.- A >> A' : s -> 
  (* derivable *) e |.- A' : Srt s -> e |.- A : Srt s ->
  forall s', (A :: e) |.- B >> B' : s' ->
  (* derivable *) A :: e |.- B : Srt s' -> A' :: e |.- B' : Srt s' ->
  forall s'', sum_sort s s' s'' -> sum_sort s s' s'' ->
  e |.- (Sum A B) >> (Sum A' B') : s''

  | coerce_sub_l : forall e U P U', 
  e |.- U >> U' : set ->
  (* derivable *) U :: e |.- P : Srt prop ->
  e |.- Subset U P >> U' : set

  | coerce_sub_r : forall e U U' P,
  e |.- U >> U' : set -> 
  (* derivable *) U' :: e |.- P : Srt prop ->
  e |.- U >> (Subset U' P) : set

  | coerce_conv : forall e A B C D s,
  e |.- A : Srt s -> e |.- B : Srt s -> e |.- C : Srt s -> e |.- D : Srt s ->
  conv A B -> e |.- B >> C : s -> conv C D -> e |.- A >> D : s

where "G |.- T >> U : s" := (coerce G T U s)

with wf : env -> Prop :=
  | wf_nil : wf nil
  | wf_var : forall e T s, e |.- T : (Srt s) -> wf (T :: e)

with typ : env -> term -> term -> Prop :=
  | type_prop : forall e, wf e -> e |.- (Srt prop) : (Srt kind)
  | type_set : forall e, wf e -> e |.- (Srt set) : (Srt kind)	
  | type_var : (* start *)
      forall e, wf e -> forall n T, item_lift T e n -> e |.- (Ref n) : T
  | type_abs :
      forall e T s1,
      e |.- T : (Srt s1) ->
      forall M (U : term) s2,
      (T :: e) |.- U : (Srt s2) ->
      (T :: e) |.- M : U -> 
      e |.- (Abs T M) : (Prod T U)
  | type_app :
      forall e v (V : term), e |.- v : V ->
      forall u (Ur : term), e |.- u : (Prod V Ur) -> 
      e |.- (App u v) : (subst v Ur)	

  | type_pair :
    forall e (U : term) s1, e |.- U : (Srt s1) ->
    forall u, e |.- u : U ->
    forall V s2, (U :: e) |.- V : (Srt s2) ->
    forall v, e |.- v : (subst u V) -> 
    forall s3, sum_sort s1 s2 s3 ->
    e |.- (Pair (Sum U V) u v) : (Sum U V)

  | type_prod :
      forall e T s1,
      e |.- T : (Srt s1) ->
      forall (U : term) s2,
      (T :: e) |.- U : (Srt s2) -> 
      e |.- (Prod T U) : (Srt s2)

  | type_sum :
      forall e T s1,
      e |.- T : (Srt s1) ->
      forall (U : term) s2,
      (T :: e) |.- U : (Srt s2) -> 
      forall s3, sum_sort s1 s2 s3 ->
      e |.- (Sum T U) : Srt s3

  | type_subset : 
      forall e T, e |.- T : (Srt set) ->
      forall (U : term), (T :: e) |.- U : (Srt prop) -> 
      e |.- (Subset T U) : (Srt set)

  | type_pi1 :
      forall e t U V, e |.- t : (Sum U V) -> 
      e |.- (Pi1 t) : U

  | type_pi2 :
      forall e t U V, e |.- t : (Sum U V) -> 
      e |.- (Pi2 t) : (subst (Pi1 t) V)

  | type_conv :
      forall e t (U V : term),
      e |.- t : U -> 
      forall s, e |.- V : (Srt s) -> e |.- U : (Srt s) -> 
      e |.- U >> V : s -> 
      e |.- t : V

where "G |.- T : U" :=  (typ G T U).

Hint Resolve coerce_refl coerce_conv coerce_prod coerce_sum coerce_sub_l coerce_sub_r : coc.
Hint Resolve type_pi1 type_pi2 type_pair type_prop type_set type_var: coc.
Hint Resolve wf_nil : coc.

Scheme typ_dep := Induction for typ Sort Prop.

Scheme typ_wf_mut := Induction for typ Sort Prop
with wf_typ_mut := Induction for wf Sort Prop.

Scheme typ_coerce_mut := Induction for typ Sort Prop
with coerce_typ_mut := Induction for coerce Sort Prop.

Scheme typ_coerce_wf_mut := Induction for typ Sort Prop
with coerce_typ_wf_mut := Induction for coerce Sort Prop
with wf_typ_coerce_mut := Induction for wf Sort Prop.

Lemma double_typ_coerce_mut :
forall (P : forall (e : env) t t0, e |.- t : t0 -> Prop)
         (P0 : forall (e : env) t t0 s, e |.- t >> t0 : s -> Prop),
       (forall (e : env) (w : wf e), P e (Srt prop) (Srt kind) (type_prop w)) ->
       (forall (e : env) (w : wf e), P e (Srt set) (Srt kind) (type_set w)) ->
       (forall (e : env) (w : wf e) n T (i : item_lift T e n),
        P e (Ref n) T (type_var w i)) ->
       (forall (e : env) T s1 (t : e |.- T : Srt s1),
        P e T (Srt s1) t ->
        forall M (U : term) s2 (t0 : T :: e |.- U : Srt s2),
        P (T :: e) U (Srt s2) t0 ->
        forall t1 : T :: e |.- M : U,
        P (T :: e) M U t1 -> P e (Abs T M) (Prod T U) (type_abs t t0 t1)) ->
       (forall (e : env) v (V : term) (t : e |.- v : V),
        P e v V t ->
        forall u (Ur : term) (t0 : e |.- u : Prod V Ur),
        P e u (Prod V Ur) t0 -> P e (App u v) (subst v Ur) (type_app t t0)) ->
       (forall (e : env) (U : term) s1 (t : e |.- U : Srt s1),
        P e U (Srt s1) t ->
        forall u (t0 : e |.- u : U),
        P e u U t0 ->
        forall (V : term) s2 (t1 : U :: e |.- V : Srt s2),
        P (U :: e) V (Srt s2) t1 ->
        forall v (t2 : e |.- v : subst u V),
        P e v (subst u V) t2 ->
        forall s3 (s : sum_sort s1 s2 s3),
        P e (Pair (Sum U V) u v) (Sum U V) (type_pair t t0 t1 t2 s)) ->
       (forall (e : env) T s1 (t : e |.- T : Srt s1),
        P e T (Srt s1) t ->
        forall (U : term) s2 (t0 : T :: e |.- U : Srt s2),
        P (T :: e) U (Srt s2) t0 -> P e (Prod T U) (Srt s2) (type_prod t t0)) ->
       (forall (e : env) T s1 (t : e |.- T : Srt s1),
        P e T (Srt s1) t ->
        forall (U : term) s2 (t0 : T :: e |.- U : Srt s2),
        P (T :: e) U (Srt s2) t0 ->
        forall s3 (s : sum_sort s1 s2 s3),
        P e (Sum T U) (Srt s3) (type_sum t t0 s)) ->
       (forall (e : env) T (t : e |.- T : Srt set),
        P e T (Srt set) t ->
        forall (U : term) (t0 : T :: e |.- U : Srt prop),
        P (T :: e) U (Srt prop) t0 ->
        P e (Subset T U) (Srt set) (type_subset t t0)) ->
       (forall (e : env) t (U V : term) (t0 : e |.- t : Sum U V),
        P e t (Sum U V) t0 -> P e (Pi1 t) U (type_pi1 t0)) ->
       (forall (e : env) t (U V : term) (t0 : e |.- t : Sum U V),
        P e t (Sum U V) t0 -> P e (Pi2 t) (subst (Pi1 t) V) (type_pi2 t0)) ->
       (forall (e : env) t (U V : term) (t0 : e |.- t : U),
        P e t U t0 ->
        forall s (t1 : e |.- V : Srt s),
        P e V (Srt s) t1 ->
        forall t2 : e |.- U : Srt s,
        P e U (Srt s) t2 ->
        forall c : e |.- U >> V : s,
        P0 e U V s c -> P e t V (type_conv t0 t1 t2 c)) ->
       (forall (e : env) A s (t : e |.- A : Srt s),
        P e A (Srt s) t -> P0 e A A s (coerce_refl t)) ->
       (forall (e : env) A B A' B' s (c : e |.- A' >> A : s),
        P0 e A' A s c ->
        forall t : e |.- A' : Srt s,
        P e A' (Srt s) t ->
        forall t0 : e |.- A : Srt s,
        P e A (Srt s) t0 ->
        forall s' (c0 : A' :: e |.- B >> B' : s'),
        P0 (A' :: e) B B' s' c0 ->
        forall t1 : A :: e |.- B : Srt s',
        P (A :: e) B (Srt s') t1 ->
        forall t2 : A' :: e |.- B' : Srt s',
        P (A' :: e) B' (Srt s') t2 ->
        P0 e (Prod A B) (Prod A' B') s' (coerce_prod c t t0 c0 t1 t2)) ->
       (forall (e : env) A B A' B' s (c : e |.- A >> A' : s),
        P0 e A A' s c ->
        forall t : e |.- A' : Srt s,
        P e A' (Srt s) t ->
        forall t0 : e |.- A : Srt s,
        P e A (Srt s) t0 ->
        forall s' (c0 : A :: e |.- B >> B' : s'),
        P0 (A :: e) B B' s' c0 ->
        forall t1 : A :: e |.- B : Srt s',
        P (A :: e) B (Srt s') t1 ->
        forall t2 : A' :: e |.- B' : Srt s',
        P (A' :: e) B' (Srt s') t2 ->
        forall s'' (s0 s1 : sum_sort s s' s''),
        P0 e (Sum A B) (Sum A' B') s'' (coerce_sum c t t0 c0 t1 t2 s0 s1)) ->
       (forall (e : env) (U P1 U' : term) (c : e |.- U >> U' : set),
        P0 e U U' set c ->
        forall t : U :: e |.- P1 : Srt prop,
        P (U :: e) P1 (Srt prop) t ->
        P0 e (Subset U P1) U' set (coerce_sub_l c t)) ->
       (forall (e : env) (U U' P1 : term) (c : e |.- U >> U' : set),
        P0 e U U' set c ->
        forall t : U' :: e |.- P1 : Srt prop,
        P (U' :: e) P1 (Srt prop) t ->
        P0 e U (Subset U' P1) set (coerce_sub_r c t)) ->
       (forall (e : env) A B (C D : term) s (t : e |.- A : Srt s),
        P e A (Srt s) t ->
        forall t0 : e |.- B : Srt s,
        P e B (Srt s) t0 ->
        forall t1 : e |.- C : Srt s,
        P e C (Srt s) t1 ->
        forall t2 : e |.- D : Srt s,
        P e D (Srt s) t2 ->
        forall (c : conv A B) (c0 : e |.- B >> C : s),
        P0 e B C s c0 ->
        forall c1 : conv C D, P0 e A D s (coerce_conv t t0 t1 t2 c c0 c1)) ->
       (forall (e : env) t t0 (c : e |.- t : t0 ), P e t t0 c)
       /\ (forall (e : env) t t0 s (c : e |.- t >> t0 : s), P0 e t t0 s c).
Proof.
  intros.
  split.
  intros ; eapply typ_coerce_mut with (P:=P) (P0:=P0) ; auto ; auto.
  intros ; eapply coerce_typ_mut with (P:=P) (P0:=P0) ; auto ; auto.
Qed.

Lemma double_typ_coerce_wf_mut :
forall (P : forall (e : env) t t0, e |.- t : t0 -> Prop)
         (P0 : forall (e : env) t t0 s, e |.- t >> t0 : s -> Prop)
         (P1 : forall e : env, wf e -> Prop),
       (forall (e : env) (w : wf e),
        P1 e w -> P e (Srt prop) (Srt kind) (type_prop w)) ->
       (forall (e : env) (w : wf e),
        P1 e w -> P e (Srt set) (Srt kind) (type_set w)) ->
       (forall (e : env) (w : wf e),
        P1 e w ->
        forall n T (i : item_lift T e n), P e (Ref n) T (type_var w i)) ->
       (forall (e : env) T s1 (t : e |.- T : Srt s1),
        P e T (Srt s1) t ->
        forall M (U : term) s2 (t0 : T :: e |.- U : Srt s2),
        P (T :: e) U (Srt s2) t0 ->
        forall t1 : T :: e |.- M : U,
        P (T :: e) M U t1 -> P e (Abs T M) (Prod T U) (type_abs t t0 t1)) ->
       (forall (e : env) v (V : term) (t : e |.- v : V),
        P e v V t ->
        forall u (Ur : term) (t0 : e |.- u : Prod V Ur),
        P e u (Prod V Ur) t0 -> P e (App u v) (subst v Ur) (type_app t t0)) ->
       (forall (e : env) (U : term) s1 (t : e |.- U : Srt s1),
        P e U (Srt s1) t ->
        forall u (t0 : e |.- u : U),
        P e u U t0 ->
        forall (V : term) s2 (t1 : U :: e |.- V : Srt s2),
        P (U :: e) V (Srt s2) t1 ->
        forall v (t2 : e |.- v : subst u V),
        P e v (subst u V) t2 ->
        forall s3 (s : sum_sort s1 s2 s3),
        P e (Pair (Sum U V) u v) (Sum U V) (type_pair t t0 t1 t2 s)) ->
       (forall (e : env) T s1 (t : e |.- T : Srt s1),
        P e T (Srt s1) t ->
        forall (U : term) s2 (t0 : T :: e |.- U : Srt s2),
        P (T :: e) U (Srt s2) t0 -> P e (Prod T U) (Srt s2) (type_prod t t0)) ->
       (forall (e : env) T s1 (t : e |.- T : Srt s1),
        P e T (Srt s1) t ->
        forall (U : term) s2 (t0 : T :: e |.- U : Srt s2),
        P (T :: e) U (Srt s2) t0 ->
        forall s3 (s : sum_sort s1 s2 s3),
        P e (Sum T U) (Srt s3) (type_sum t t0 s)) ->
       (forall (e : env) T (t : e |.- T : Srt set),
        P e T (Srt set) t ->
        forall (U : term) (t0 : T :: e |.- U : Srt prop),
        P (T :: e) U (Srt prop) t0 ->
        P e (Subset T U) (Srt set) (type_subset t t0)) ->
       (forall (e : env) t (U V : term) (t0 : e |.- t : Sum U V),
        P e t (Sum U V) t0 -> P e (Pi1 t) U (type_pi1 t0)) ->
       (forall (e : env) t (U V : term) (t0 : e |.- t : Sum U V),
        P e t (Sum U V) t0 -> P e (Pi2 t) (subst (Pi1 t) V) (type_pi2 t0)) ->
       (forall (e : env) t (U V : term) (t0 : e |.- t : U),
        P e t U t0 ->
        forall s (t1 : e |.- V : Srt s),
        P e V (Srt s) t1 ->
        forall t2 : e |.- U : Srt s,
        P e U (Srt s) t2 ->
        forall c : e |.- U >> V : s,
        P0 e U V s c -> P e t V (type_conv t0 t1 t2 c)) ->
       (forall (e : env) A s (t : e |.- A : Srt s),
        P e A (Srt s) t -> P0 e A A s (coerce_refl t)) ->
       (forall (e : env) A B A' B' s (c : e |.- A' >> A : s),
        P0 e A' A s c ->
        forall t : e |.- A' : Srt s,
        P e A' (Srt s) t ->
        forall t0 : e |.- A : Srt s,
        P e A (Srt s) t0 ->
        forall s' (c0 : A' :: e |.- B >> B' : s'),
        P0 (A' :: e) B B' s' c0 ->
        forall t1 : A :: e |.- B : Srt s',
        P (A :: e) B (Srt s') t1 ->
        forall t2 : A' :: e |.- B' : Srt s',
        P (A' :: e) B' (Srt s') t2 ->
        P0 e (Prod A B) (Prod A' B') s' (coerce_prod c t t0 c0 t1 t2)) ->
       (forall (e : env) A B A' B' s (c : e |.- A >> A' : s),
        P0 e A A' s c ->
        forall t : e |.- A' : Srt s,
        P e A' (Srt s) t ->
        forall t0 : e |.- A : Srt s,
        P e A (Srt s) t0 ->
        forall s' (c0 : A :: e |.- B >> B' : s'),
        P0 (A :: e) B B' s' c0 ->
        forall t1 : A :: e |.- B : Srt s',
        P (A :: e) B (Srt s') t1 ->
        forall t2 : A' :: e |.- B' : Srt s',
        P (A' :: e) B' (Srt s') t2 ->
        forall s'' (s0 s1 : sum_sort s s' s''),
        P0 e (Sum A B) (Sum A' B') s'' (coerce_sum c t t0 c0 t1 t2 s0 s1)) ->
       (forall (e : env) (U P2 U' : term) (c : e |.- U >> U' : set),
        P0 e U U' set c ->
        forall t : U :: e |.- P2 : Srt prop,
        P (U :: e) P2 (Srt prop) t ->
        P0 e (Subset U P2) U' set (coerce_sub_l c t)) ->
       (forall (e : env) (U U' P2 : term) (c : e |.- U >> U' : set),
        P0 e U U' set c ->
        forall t : U' :: e |.- P2 : Srt prop,
        P (U' :: e) P2 (Srt prop) t ->
        P0 e U (Subset U' P2) set (coerce_sub_r c t)) ->
       (forall (e : env) A B (C D : term) s (t : e |.- A : Srt s),
        P e A (Srt s) t ->
        forall t0 : e |.- B : Srt s,
        P e B (Srt s) t0 ->
        forall t1 : e |.- C : Srt s,
        P e C (Srt s) t1 ->
        forall t2 : e |.- D : Srt s,
        P e D (Srt s) t2 ->
        forall (c : conv A B) (c0 : e |.- B >> C : s),
        P0 e B C s c0 ->
        forall c1 : conv C D, P0 e A D s (coerce_conv t t0 t1 t2 c c0 c1)) ->
       P1 nil wf_nil ->
       (forall (e : env) T s (t : e |.- T : Srt s),
        P e T (Srt s) t -> P1 (T :: e) (wf_var t)) ->
     (forall (e : env) t t0 (t1 : e |.- t : t0), P e t t0 t1) /\
     (forall (e : env) t t0 s (t1 : e |.- t >> t0 : s), P0 e t t0 s t1) /\
     (forall (e : env) (t1 : wf e), P1 e t1).
Proof.
  intros.
  split.
  intros ; eapply typ_coerce_wf_mut with (P:=P) (P0:=P0) (P1:=P1) ; auto ; auto.
  split ; intros.
  eapply coerce_typ_wf_mut with (P:=P) (P0:=P0) (P1 := P1) ; auto ; auto.
  eapply wf_typ_coerce_mut with (P:=P) (P0:=P0) (P1 := P1) ; auto ; auto.
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


Lemma typ_wf : forall e t T, e |.- t : T -> wf e.
simple induction 1; auto with coc core arith datatypes.
Qed.


  Lemma wf_sort :
   forall n e f,
   trunc _ (S n) e f ->
   wf e -> forall t, item _ t e n -> exists s : sort, f |.- t : (Srt s).
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

Lemma typ_sort_aux : forall G t T, G |.- t : T -> 
  forall s, t = (Srt s) -> is_prop s /\ T = (Srt kind).
Proof.
induction 1 ; intros ; try discriminate.

injection H0 ; intro ; rewrite <- H1 ; unfold is_prop ; intuition.

injection H0 ; intro ; rewrite <- H1 ; unfold is_prop ; intuition.

induction (IHtyp1 s0 H3).
split ; auto.

destruct (IHtyp3 _ H5).
unfold is_prop in H6.
induction H6 ; discriminate.
Qed.

Lemma typ_sort : forall G s T, G |.- (Srt s) : T -> is_prop s /\ T = (Srt kind).
Proof.
intros.
apply (typ_sort_aux H (refl_equal (Srt s))).
Qed.

Lemma typ_not_kind : forall G t T, G |.- t : T -> t <> Srt kind.
Proof.
  induction 1 ; intros ; unfold not ; intros ; try discriminate ; auto with coc.
Qed.

Hint Resolve typ_not_kind typ_wf : coc.

Lemma coerce_sort : forall G T U s, 
  G |.- T >> U : s -> (G |.- T : Srt s /\ G |.- U : Srt s).
Proof.
  induction 1 ; intros ; split ; try (intuition ; intros ; auto with coc core).
  apply type_prod with s ; auto with coc core.
  apply type_prod with s ; auto with coc core.
  apply type_sum with s s' ; auto with coc core.
  apply type_sum with s s' ; auto with coc core.
  apply type_subset ; auto with coc core.
  apply type_subset ; auto with coc core.
Qed.

Lemma coerce_sort_l : forall G T U s, 
  G |.- T >> U : s -> G |.- T : Srt s.
Proof. 
  intros G T U s H.
  apply (proj1 (coerce_sort H)).
Save.

Lemma coerce_sort_r : forall G T U s, 
  G |.- T >> U : s -> G |.- U : Srt s.
Proof. 
  intros G T U s H.
  apply (proj2 (coerce_sort  H)).
Save.

Lemma coerce_prop_prop : forall e, wf e -> e |.- Srt prop >> Srt prop : kind.
Proof.
  intros.
  auto with coc.
Qed.

Lemma coerce_set_set : forall e, wf e -> e |.- Srt set >> Srt set : kind.
Proof.
  intros.
  auto with coc.
Qed.

Lemma coerce_is_prop : forall e, wf e -> forall s, is_prop s -> e |.- Srt s >> Srt s : kind.
Proof.
  intros.
  induction H0 ;
  rewrite H0 ; auto with coc.
Qed.

Lemma conv_coerce : forall e T T' s, e |.- T : Srt s -> e |.- T' : Srt s -> conv T T' ->
  e |.- T >> T' : s.
Proof.
 intros.
 apply coerce_conv with T' T' ; auto with coc.
Qed.

Hint Resolve coerce_sort_l coerce_sort_r coerce_prop_prop coerce_set_set coerce_is_prop conv_coerce : coc.
