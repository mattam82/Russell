Require Import Lambda.Terms.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Export Lambda.MyList.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

  Definition env := list term.

  Implicit Types e f g : env.

  Definition item_lift t e n :=
    ex2 (fun u => t = lift (S n) u) (fun u => item term u (e:list term) n).

  Inductive wf : env -> Prop :=
    | wf_nil : wf nil
    | wf_var : forall e T s, typ e T (Srt s) -> wf (T :: e)
with typ : env -> term -> term -> Prop :=
  | type_prop : forall e, wf e -> typ e (Srt prop) (Srt kind)
  | type_set : forall e, wf e -> typ e (Srt set) (Srt kind)
  | type_var :
      forall e,
      wf e -> forall (v : nat) t, item_lift t e v -> typ e (Ref v) t
  | type_abs :
      forall e T s1,
      typ e T (Srt s1) ->
      forall M (U : term) s2,
      typ (T :: e) U (Srt s2) ->
      typ (T :: e) M U -> typ e (Abs T M) (Prod T U)
  | type_app :
      forall e v (V : term),
      typ e v V ->
      forall u (Ur : term),
      typ e u (Prod V Ur) -> typ e (App u v) (subst v Ur)	
  | type_pair :
    forall e (U : term) s1,
      typ e U (Srt s1) ->
      forall u, typ e u U ->
      forall V s2, typ (U :: e) V (Srt s2) ->
	forall v, typ e v (subst u V) -> 
	  typ e (Pair (Sum U V) u v) (Sum U V)
  | type_prod :
      forall e T s1,
      typ e T (Srt s1) ->
      forall (U : term) s2,
      typ (T :: e) U (Srt s2) -> typ e (Prod T U) (Srt s2)
  | type_sum :
      forall e T s1,
      typ e T (Srt s1) ->
      forall (U : term) s2,
      typ (T :: e) U (Srt s2) -> typ e (Sum T U) (Srt s2)

  | type_subset :
      forall e T s1,
      typ e T (Srt set) ->
      forall (U : term),
      typ (T :: e) U (Srt prop) -> typ e (Subset T U) (Srt set)

  | type_pi1 :
      forall e t U V,
      typ e t (Sum U V) -> typ e (Pi1 t) U

  | type_pi2 :
      forall e t U V,
      typ e t (Sum U V) -> typ e (Pi2 t) (subst (Pi1 t) V)

  | type_conv :
      forall e t (U V : term),
      typ e t U -> conv U V -> forall s, typ e V (Srt s) -> typ e t V.

  Hint Resolve wf_nil type_prop type_set type_var: coc.


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


  Lemma typ_wf : forall e t T, typ e t T -> wf e.
simple induction 1; auto with coc core arith datatypes.
Qed.


  Lemma wf_sort :
   forall n e f,
   trunc _ (S n) e f ->
   wf e -> forall t, item _ t e n -> exists s : sort, typ f t (Srt s).
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

