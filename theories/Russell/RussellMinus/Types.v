Require Import Termes.
Require Import LiftSubst.
Require Import Reduction.
Require Import Conv.
Require Import Env.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Types A B M N T t u v : term.

Reserved Notation "G ||- T : s" (at level 70, T, s at next level).

Inductive type : Set :=
  | orig_set : type
  | orig_prop : type
  | kind_prop : type
  | kind_set : type
  | triangle_set : type
  | triangle_prop : type.

Definition is_orig (t : type) := t <> triangle_set /\ t <> triangle_prop.

Definition interp (t : type) : is_orig t -> type.
induction t ; intros.
exact triangle_set.
exact triangle_prop.
exact orig_prop.
exact orig_set.
unfold is_orig in H ; simpl in H.
intuition.
unfold is_orig in H ; simpl in H.
intuition.
Defined.

Lemma is_orig_set : is_orig orig_set.
Proof.
  unfold is_orig ; simpl ; auto ; intuition ; discriminate.
Qed.

Lemma is_orig_prop : is_orig orig_prop.
Proof.
  unfold is_orig ; simpl ; auto ; intuition ; discriminate.
Qed.

Lemma is_orig_kind_prop : is_orig kind_prop.
Proof.
  unfold is_orig ; simpl ; auto ; intuition ; discriminate.
Qed.

Lemma is_orig_kind_set : is_orig kind_set.
Proof.
  unfold is_orig ; simpl ; auto ; intuition ; discriminate.
Qed.

Definition sum_sort s1 s2 s3 :=
  (s1 = orig_set /\ s2 = orig_set /\ s3 = orig_set) \/
  (s1 = kind_set /\ s2 = orig_set /\ s3 = kind_set) \/
  (s1 = orig_set /\ s2 = kind_set /\ s3 = kind_set) \/
  (s1 = orig_set /\ s2 = kind_prop /\ s3 = kind_prop) \/
  (s1 = orig_prop /\ s2 = orig_prop /\ s3 = orig_prop).


Inductive wf_minus : env -> Prop :=
  | wf_nil : wf_minus nil
  | wf_var_set : forall e T s, e ||- T : s -> is_orig s -> wf_minus (T :: e)

with typ_minus : env -> term -> type -> Prop :=
  | type_minus_prop : forall e, wf_minus e -> e ||- (Srt prop) : kind_prop
  | type_minus_set : forall e, wf_minus e -> e ||- (Srt set) : kind_set

  | type_minus_var : (* start *)
  forall e, wf_minus e -> forall n T, item_lift T e n ->
  forall s, e ||- T : s -> forall H : is_orig s, e ||- (Ref n) : interp H

  | type_minus_abs :
    forall e T B s, e ||- Prod T B : s ->
    forall H : is_orig s, 
    forall M, (T :: e) ||- M : interp H -> 
    e ||- (Abs T M) : interp H

  | type_minus_app :
      forall e v s1, e ||- v : s1 ->
      forall u s, e ||- u : s -> 
      e ||- (App u v) : s

  | type_minus_pair :
    forall e (U : term) s1, e ||- U : s1 ->
    forall u su, e ||- u : su ->
    forall V s2, (U :: e) ||- V : s2 ->
    forall v, e ||- v : s2 -> 
    forall s3, sum_sort s1 s2 s3 ->
    e ||- (Pair (Sum U V) u v) : s3

  | type_minus_prod :
      forall e T s1,
      e ||- T : s1 ->
      forall (U : term) s2,
      (T :: e) ||- U : s2 -> 
      is_orig s1 -> is_orig s2 ->
      e ||- (Prod T U) : s2

  | type_minus_sum :
      forall e T s1,
      e ||- T : s1 ->
      forall (U : term) s2,
      (T :: e) ||- U : s2 -> 
      forall s3, sum_sort s1 s2 s3 ->
      e ||- (Sum T U) : s3

  | type_minus_subset : 
      forall e T, e ||- T : orig_set ->
      forall (U : term), (T :: e) ||- U : orig_prop -> 
      e ||- (Subset T U) : orig_set

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
Require Import CCPD.Thinning.
Require Import CCPD.Generation.

Lemma soundness : forall G (t : term) T, G |- t : T ->
 ((G |- T : (Srt set) -> G ||- t : triangle_set) /\
 (G |- T : (Srt prop) -> G ||- t : triangle_prop) /\
 (G |- T : Srt kind -> G ||- t : orig_set \/ G ||- t : orig_prop) /\
 (T = Srt kind -> G ||- t : kind_set \/ G ||- t : kind_prop)).
Proof.
  induction 1 using typ_wf_mut with
  (P := fun G t (T : term) => fun H0 : G |- t : T =>
 ((G |- T : (Srt set) -> G ||- t : triangle_set) /\
 (G |- T : (Srt prop) -> G ||- t : triangle_prop) /\
 (G |- T : Srt kind -> G ||- t : orig_set \/ G ||- t : orig_prop) /\
 (T = Srt kind -> G ||- t : kind_set \/ G ||- t : kind_prop)))
  (P0 := fun G => fun H : wf G => 
  wf_minus G /\
  forall T G n, item_lift T G n -> 
  (G |- T : Srt set -> G ||- T : orig_set) /\
  (G |- T : Srt prop -> G ||- T : orig_prop) /\
  (G |- T : Srt kind -> G ||- T : kind_set \/ G ||- T : kind_prop))
 ; simpl ; intros.
  
  intuition ; intros.
  elim (typ_not_kind H1) ; auto.
  elim (typ_not_kind H1) ; auto.

  intuition ; intros.
  elim (typ_not_kind H1) ; auto.

  intuition ; intros.
  elim (typ_not_kind H1) ; auto.
  elim (typ_not_kind H1) ; auto.
  elim (typ_not_kind H1) ; auto.

  split ; intros.
  destruct IHtyp.
  destruct (H1 T e n i).
  pose (H2 H).
  pose (type_minus_var H0 i t (is_orig_set)).
  simpl in t0 ; assumption.

  split ; intros.
  destruct IHtyp.
  destruct (H1 T e n i).
  destruct H3.
  pose (H3 H).
  pose (type_minus_var H0 i t (is_orig_prop)).
  simpl in t0 ; assumption.

  split ; intros.
  destruct IHtyp.
  destruct (H1 T e n i).
  destruct H3.
  pose (H4 H).
  destruct o.
  left.
  pose (type_minus_var H0 i H5 (is_orig_kind_set)).
  simpl in t ; assumption.

  right.
  pose (type_minus_var H0 i H5 (is_orig_kind_prop)).
  simpl in t ; assumption.

  destruct (wf_sort_lift w i).
  rewrite H in H0.
  elim (typ_not_kind H0) ; auto.


  split ; intros.
  intuition.

  pose (generation_prod2 H2).
  destruct a.
  pose (H7 H16).
  destruct (type_sorted H).
  cut (e ||- Prod T U : orig_set) ; intros.
  assert(triangle_set = interp is_orig_set).
  simpl ; auto.
  rewrite H19.
  apply (@type_minus_abs e T U orig_set H18).
  simpl ; auto.
  pose (H13 H17).
  destruct o.
  eapply type_minus_prod with kind_set ; auto.
  
 with orig_set.
  with kind_set ; auto with coc.


.

  unfold is_prop in H0 ; intuition ; try discriminate.



