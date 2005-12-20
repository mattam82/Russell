Require Import Termes.
Require Import LiftSubst.
Require Import Reduction.
Require Import Conv.
Require Import Env.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Reserved Notation "G |- T >> U" (at level 70, T, U at next level).

Reserved Notation "G |- T : U" (at level 70, T, U at next level).
  Inductive wf : env -> Prop :=
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

  | type_let_in :
      forall e t U, e |- t : U ->
      forall s1, e |- U : (Srt s1) -> (* Just for easier induction, derivable from the next 
	 judgment *)
      forall v M, (U :: e) |- v : M -> 
      forall s2, (U :: e) |- M : (Srt s2) ->
      e |- (Let_in t v) : (subst t M)

  | type_conv :
      forall e t (U V : term),
      e |- t : U -> 
      forall s, e |- V : (Srt s) -> e |- U : (Srt s) -> 
      e |- U >> V -> 
      e |- t : V

where "G |- T : U" :=  (typ G T U)

with coerce : env -> term -> term -> Prop :=
  | coerce_refl : forall G A, G |- A >> A

  | coerce_prod : forall G A B A' B', 
  forall s, G |- A' : (Srt s) -> G |- A : (Srt s) -> G |- A' >> A -> 
  (A' :: G) |- B >> B' -> G |- (Prod A B) >> (Prod A' B')
  
  | coerce_sum : forall G A B A' B', 
  forall s, G |- A' : (Srt s) -> G |- A : (Srt s) -> G |- A >> A' -> 
  (A :: G) |- B >> B' -> G |- (Sum A B) >> (Sum A' B')

  | coerce_sub_l : forall G U P U', G |- U >> U' -> 
  G |- (Subset U P) >> U'

  | coerce_sub_r : forall G U U' P, G |- U >> U' -> 
  G |- U >> (Subset U' P)

  | coerce_beta : forall G A B C D, 
  forall s, G |- A : (Srt s) -> G |- B : (Srt s) -> G |- C : (Srt s) ->
  G |- D : (Srt s) ->
  conv A B -> G |- B >> C -> conv C D -> G |- A >> D

where "G |- T >> U" := (coerce G T U).

Hint Resolve coerce_refl coerce_prod coerce_sum coerce_sub_l coerce_sub_r : coc.
Hint Resolve type_pi1 type_pi2 type_pair type_prop type_set type_var: coc.

Scheme typ_mut := Induction for typ Sort Prop
with coerce_mut := Induction for coerce Sort Prop.

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
