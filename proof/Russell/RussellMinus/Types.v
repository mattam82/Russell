Require Import Termes.
Require Import LiftSubst.
Require Import Reduction.
Require Import Conv.
Require Import Env.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type t : sort.
Implicit Types A B M N T u v : term.

Reserved Notation "G ||- T : s" (at level 70, T, s at next level).

Inductive type : Set :=
  | in_set : type
  | in_prop : type
  | star : type
  | box : type.

Definition interp (s : sort) : type :=
  match s with
  | prop => in_prop
  | set => in_set
  | kind => star
  end.

Definition sum_sort' s1 s2 s3 :=
  (s1 = in_set /\ s2 = in_set /\ s3 = in_set) \/
  (s1 = star /\ s2 = in_set /\ s3 = star) \/
  (s1 = in_set /\ s2 = star /\ s3 = star) \/
  (s1 = in_prop /\ s2 = in_prop /\ s3 = in_prop).

Inductive wf_minus : env -> Prop :=
  | wf_nil : wf_minus nil
  | wf_var : forall e T s, e ||- T : s -> wf_minus (T :: e)

with typ_minus : env -> term -> type -> Prop :=
  | type_minus_prop : forall e, wf_minus e -> e ||- (Srt prop) : star
  | type_minus_set : forall e, wf_minus e -> e ||- (Srt set) : star

  | type_minus_var : (* start *)
  forall e, wf_minus e -> forall n T, item_lift T e n ->
  forall s, e ||- T : s -> e ||- (Ref n) : s

  | type_minus_abs :
      forall e T s1,
      e ||- T : s1 ->
      forall M (U : term) s2,
      (T :: e) ||- U : s2 ->
      (T :: e) ||- M : s2 -> 
      e ||- (Abs T M) : s2
  | type_minus_app :
      forall e v s1, e ||- v : s1 ->
      forall u s, e ||- u : s -> 
      e ||- (App u v) : s

  | type_minus_pair :
    forall e (U : term) s1, e ||- U : s1 ->
    forall u su, e ||- u : su ->
    forall V s2, (U :: e) ||- V : s2 ->
    forall v, e ||- v : s2 -> 
    forall s3, sum_sort' s1 s2 s3 ->
    e ||- (Pair (Sum U V) u v) : s3

  | type_minus_prod :
      forall e T s1,
      e ||- T : s1 ->
      forall (U : term) s2,
      (T :: e) ||- U : s2 -> 
      e ||- (Prod T U) : s2

  | type_minus_sum :
      forall e T s1,
      e ||- T : s1 ->
      forall (U : term) s2,
      (T :: e) ||- U : s2 -> 
      forall s3, sum_sort' s1 s2 s3 ->
      e ||- (Sum T U) : s3

  | type_minus_subset : 
      forall e T, e ||- T : in_set ->
      forall (U : term), (T :: e) ||- U : in_prop -> 
      e ||- (Subset T U) : in_set

  | type_minus_pi1 :
      forall e (t : term) s, e ||- t : s -> 
      e ||- (Pi1 t) : s

  | type_minus_pi2 :
      forall e (t : term) s, e ||- t : s -> 
      e ||- (Pi2 t) : s

(*  | type_minus_let_in :
      forall e t U, e ||- t : U ->
      forall s1, e ||- U : (Srt s1) -> (* Just for easier induction, derivable from the next 
	 judgment *)
      forall v M, (U :: e) ||- v : M -> 
      forall s2, (U :: e) ||- M : (Srt s2) ->
      e ||- (Let_in t v) : (subst t M) *)

where "G ||- T : U" :=  (typ_minus G T U).

Hint Resolve type_minus_pi1 type_minus_pi2 type_minus_pair type_minus_prop type_minus_set type_minus_var: coc.

Require Import CCPD.Types.

Lemma soundness : forall G (t : term) T, G |- t : T ->
  (forall s, G |- T : (Srt s) -> is_prop s -> G ||- t : (interp s)).
Proof.
  induction 1 ; simpl ; intros.

  elim (typ_not_kind H0) ; auto.

  elim (typ_not_kind H0) ; auto.

  induction s ; simpl ; auto with coc.
  unfold is_prop in H2 ; intuition ; try discriminate.
  apply type_minus_var with T ; auto with coc.
  unfold is_prop in H2 ; intuition ; try discriminate.



