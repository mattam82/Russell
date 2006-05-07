Require Import Termes.
Require Import LiftSubst.
Require Import Reduction.
Require Import Conv.
Require Import Env.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Reserved Notation "G |- T >> U : s" (at level 70, T, U, s at next level).
Reserved Notation "G |- T : U" (at level 70, T, U at next level).

Definition sum_sort U V s1 s2 :=
  (U = Srt set /\ V = Srt set) \/
  (s1 = set /\ s2 = set).


Lemma sum_sort_lift : forall T U s1 s2, sum_sort T U s1 s2 ->
  forall n n' k k', sum_sort (lift_rec n T k) (lift_rec n' U k') s1 s2.
Proof.
  unfold sum_sort ; intros.
  destruct H.
  induction H ; rewrite H ; auto with coc.
  rewrite H0 ; auto with coc.

  induction H ; rewrite H ; rewrite H0 ; auto with coc.
Qed.

Lemma sum_sort_subst : forall T U s1 s2, sum_sort T U s1 s2 ->
  forall t k k', sum_sort (subst_rec t T k) (subst_rec t U k') s1 s2.
Proof.
  unfold sum_sort ; intros.
  destruct H.
  induction H ; rewrite H ; rewrite H0 ; auto with coc.
  induction H ; rewrite H ; rewrite H0 ; auto with coc.
Qed.

Inductive coerce : env -> term -> term -> sort -> Prop :=
  | coerce_conv : forall e A B s, e |- A : Srt s -> e |- B : Srt s -> 
	conv A B -> e |- A >> B : s

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
  sum_sort A B s s' -> sum_sort A' B' s s' ->
  e |- (Sum A B) >> (Sum A' B') : s'

  | coerce_sub_l : forall e U P U', 
  e |- U >> U' : set ->
  (* derivable *) U :: e |- P : Srt prop ->
  e |- Subset U P >> U' : set

  | coerce_sub_r : forall e U U' P,
  e |- U >> U' : set -> 
  (* derivable *) U' :: e |- P : Srt prop ->
  e |- U >> (Subset U' P) : set

  | coerce_trans : forall e A B C,
  forall s, e |- A >> B : s -> e |- B >> C : s->
  e |- A >> C : s

where "G |- T >> U : s" := (coerce G T U s)

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
    sum_sort U V s1 s2 ->
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
      sum_sort T U s1 s2 ->
      e |- (Sum T U) : (Srt s2)

  | type_subset : 
      forall e T, e |- T : (Srt set) ->
      forall (U : term), (T :: e) |- U : (Srt prop) -> 
      e |- (Subset T U) : (Srt set)

  | type_pi1 :
      forall e t U V, e |- t : (Sum U V) -> e |- (Pi1 t) : U

  | type_pi2 :
      forall e t U V, e |- t : (Sum U V) -> 
      e |- (Pi2 t) : (subst (Pi1 t) V)

(*  | type_let_in :
      forall e t U, e |- t : U ->
      forall s1, e |- U : (Srt s1) -> (* Just for easier induction, derivable from the next 
	 judgment *)
      forall v M, (U :: e) |- v : M -> 
      forall s2, (U :: e) |- M : (Srt s2) ->
      e |- (Let_in t v) : (subst t M) *)

  | type_conv :
      forall e t (U V : term),
      e |- t : U -> 
      forall s, e |- V : (Srt s) -> e |- U : (Srt s) -> 
      e |- U >> V : s -> 
      e |- t : V

where "G |- T : U" :=  (typ G T U).

Hint Resolve coerce_conv coerce_prod coerce_sum coerce_sub_l coerce_sub_r : coc.
Hint Resolve type_pi1 type_pi2 type_pair type_prop type_set type_var: coc.

Scheme typ_mut := Induction for typ Sort Prop
with coerce_mut := Induction for coerce Sort Prop.

Scheme typ_mutwf := Induction for typ Sort Prop
with coerce_mutwf := Induction for coerce Sort Prop
with wf_mut := Induction for wf Sort Prop.

Lemma not_t_let_in : forall G t T, G |- t : T -> forall u v, t <> Let_in u v.
Proof.
  simple induction 1 ; intros ; auto with coc core arith datatypes ; try discriminate.
Qed.

  Lemma type_prop_set :
   forall s, is_prop s -> forall e, wf e -> typ e (Srt s) (Srt kind).
simple destruct 1; intros; rewrite H0.
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

Lemma typ_sort_aux : forall G t T, G |- t : T -> 
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

Lemma typ_sort : forall G s T, G |- (Srt s) : T -> is_prop s /\ T = (Srt kind).
Proof.
intros.
apply (typ_sort_aux G (Srt s) T H s (refl_equal (Srt s))).
Qed.

Lemma typ_not_kind : forall G t T, G |- t : T -> t <> Srt kind.
Proof.
  induction 1 ; intros ; unfold not ; intros ; try discriminate ; auto with coc.
Qed.

Lemma coerce_sort : forall G T U s, 
  G |- T >> U : s -> (G |- T : Srt s /\ G |- U : Srt s).
Proof.
  induction 1 ; intros ; split ; try (intuition ; intros ; auto with coc core).
  apply type_prod with s ; auto with coc core.
  apply type_prod with s ; auto with coc core.
  apply type_sum with s ; auto with coc core.
  apply type_sum with s ; auto with coc core.
  apply type_subset ; auto with coc core.
  apply type_subset ; auto with coc core.
Qed.

Lemma coerce_sort_l : forall G T U s, 
  G |- T >> U : s -> G |- T : Srt s.
Proof. 
  intros G T U s H.
  apply (proj1 (coerce_sort G T U s H)).
Save.

Lemma coerce_sort_r : forall G T U s, 
  G |- T >> U : s -> G |- U : Srt s.
Proof. 
  intros G T U s H.
  apply (proj2 (coerce_sort G T U s H)).
Save.

Hint Resolve coerce_sort_l coerce_sort_r : coc.
