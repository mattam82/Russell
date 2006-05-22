Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.Reduction.
Require Import Russell.Types.
Require Import Russell.Thinning.
Require Import Russell.Substitution.
Require Import Russell.Coercion.
Require Import Russell.GenerationNotKind.
Require Import Russell.Generation.
Require Import Russell.GenerationCoerce.
Require Import Russell.GenerationRange.
Require Import Russell.UnicityOfSorting.
Require Import Russell.Transitivity.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Definition inv_type (P : Prop) e t T : Prop :=
    match t with
    | Srt prop => T = (Srt kind) -> P
    | Srt set => T = (Srt kind) -> P
    | Srt kind => True
    | Ref n => forall x : term, item _ x e n -> 
      forall s, e |- T >> (lift (S n) x) : s -> P
    | Abs A M =>
        forall s1 (U : term),
        typ e A (Srt s1) ->
        typ (A :: e) M U -> 
        forall s, coerce e T (Prod A U) s -> P
    | App u v =>
        forall Ur V : term,
        typ e v V -> typ e u (Prod V Ur) -> 
        forall s, coerce e T (subst v Ur) s -> P
    | Pair T' u v => 
        forall U s1, typ e U (Srt s1) ->
	  typ e u U -> 
	  forall V, typ e v (subst u V) -> T' = (Sum U V) -> 
        forall s, coerce e T (Sum U V) s -> P
    | Prod A B =>
        forall s1 s2,
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) ->
        (T = Srt kind \/ coerce e T (Srt s2) kind) -> P
    | Sum A B =>
        forall s1 s2,
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) -> 
        forall s3,  sum_sort s1 s2 s3 ->
        coerce e T (Srt s3) kind -> P
    | Subset A B =>
        forall s1 s2,
        s1 = set -> s2 = prop ->
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) -> coerce e T (Srt s1) kind -> P
    | Pi1 t =>
        forall U V,
        typ e t (Sum U V) ->        
        forall s, coerce e T U s -> P
    | Pi2 t =>
        forall U V,
        typ e t (Sum U V) -> 
        forall s, coerce e T (subst (Pi1 t) V) s -> P
    end.

Lemma unicity_coerce_l : forall e U V s s', e |- U >> V : s -> e |- U : Srt s' -> e |- U >> V : s'.
Proof.
  intros.
  pose (coerce_sort_l H).
  rewrite (unique_sort H0 t).
  assumption.
Qed.

Lemma unicity_coerce_r : forall e U V s s', e |- U >> V : s -> e |- V : Srt s' -> e |- U >> V : s'.
Proof.
  intros.
  pose (coerce_sort_r H).
  rewrite (unique_sort H0 t).
  assumption.
Qed.

Hint Resolve unicity_coerce_l unicity_coerce_r : coc.


Lemma inv_type_coerce : forall (P : Prop) e t (U V : term),
  inv_type P e t U -> forall s, coerce e U V s -> inv_type P e t V.
intros P e.
cut (forall U V W s s', e |- U >> V : s -> e |- V >> W : s' -> e |- U >> W : s') ; intro Htr.
cut (forall U V W s s', e |- U >> V : s' -> e |- V >> W : s -> e |- U >> W : s') ; intro Htr2.

induction t ; simpl in |- *; intros U V H s' Hco ; intros.
destruct (coerce_sort Hco).
generalize H ; clear H.
elim s; auto with coc core arith datatypes; intros ;
rewrite H2 in H1 ; elim (typ_not_kind H1) ; auto.

apply H with x s ; auto with coc core arith datatypes.
apply Htr with V s' ; auto.

apply H with s1 U0 s'; auto with coc core arith datatypes.
apply Htr2 with V s ; auto.

apply H with Ur V0 s; auto with coc core arith datatypes.
apply Htr with V s' ; auto.

apply H with U0 s1 V0 s' ; auto with coc core arith datatypes.
apply Htr2 with V s ; auto.

apply H with s1 s2; auto with coc core arith datatypes.
destruct H2.
rewrite H2 in Hco.
elim coerce_not_kind_r with e U s' ; auto.
right.
apply Htr with V s' ; auto.

apply H with s1 s2 s3; auto with coc core arith datatypes.
apply Htr with V s' ; auto.

apply H with s1 s2 ; auto with coc core arith datatypes.
apply Htr with V s' ; auto.

apply H with U0 V0 s; auto with coc core arith datatypes.
apply Htr with V s' ; auto.

apply H with U0 V0 s'; auto with coc core arith datatypes.
apply Htr2 with V s ; auto.

intros.
eapply coerce_trans with V ; auto with coc.
apply unicity_coerce_l with s ; auto.
exact (coerce_sort_r H).

intros.
eapply coerce_trans with V ; auto with coc.
apply unicity_coerce_r with s ; auto.
exact (coerce_sort_l H0).
Qed.

Theorem typ_inversion :
  forall (P : Prop) e t T, typ e t T -> inv_type P e t T -> P.
Proof.
intros.
pose (type_sorted H).
rename H into Ht.
generalize Ht H0 o ; clear H0 o.
induction 1; simpl in |- *; intros ; 
auto with coc core arith datatypes.

elim H0; intros.
induction (wf_sort_lift H H0).
apply H1 with x x0; auto with coc core arith datatypes.
rewrite <- H2.
apply coerce_refl ; auto with coc core.

destruct o ; try discriminate.
destruct H.
apply H0 with s1 U x; auto with coc core arith datatypes.

destruct o.
pose (typ_not_kind Ht0_1).
pose (subst_to_sort _ H n).
rewrite e0 in Ht0_2.
pose (type_no_kind_prod_type Ht0_2).
simpl in t.
intuition.

destruct H.
apply H0 with Ur V x; auto with coc core arith datatypes.

destruct o ; try discriminate.
destruct H1.
apply H0 with U s1 V x; auto with coc core arith datatypes.

destruct o.
apply H0 with s1 s2 ; auto with coc.
destruct H.
apply H0 with s1 s2 ; auto with coc.
right.
destruct (typ_sort H) ; auto with coc.
cut (wf e) ; auto with coc.
apply (typ_wf H).


destruct o.
apply H0 with s1 s2 s3 ; auto with coc.
inversion H.
intuition.
rewrite H5 in H1; discriminate.
intuition.
rewrite H5 in H1; discriminate.
destruct H1.
apply H0 with s1 s2 s3 ; auto with coc.
destruct (typ_sort H1) ; auto with coc.
cut (wf e) ; auto with coc.
apply (typ_wf H1).

destruct o ; try discriminate.
destruct H.

apply H0 with set prop; auto with coc core arith datatypes.
cut (wf e) ; auto with coc.
apply (typ_wf H).

destruct o.
pose (sort_of_pi1_range Ht).
rewrite H in n.
simpl in n.
destruct (n kind (refl_equal (Srt kind))).
destruct H.
apply H0 with U V x ; auto with coc.

destruct o.
pose (sort_of_pi2_range Ht).
rewrite H in n.
simpl in n.
destruct (n kind (refl_equal (Srt kind))).
destruct H.
apply H0 with U V x ; auto with coc.

pose (coerce_sym H).
apply IHHt0_1 ; auto with coc core arith.
pose (inv_type_coerce).
cut (inv_type P e t V).
intro invt.
apply (i _ _ _ _ _ invt _ c) ; auto.
assumption.

pose (coerce_sort_l H).
right ; exists s ; auto.
Qed.


Lemma typ_sort_kind : forall G s s', G |- Srt s : Srt s' -> s' = kind.
Proof.
  intros.
  destruct (typ_sort H).
  inversion H1.
  auto.
Qed.


  Lemma inv_typ_prop : forall e T, typ e (Srt prop) T -> T = (Srt kind) .
intros.
apply typ_inversion with e (Srt prop) T ; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_set : forall e T, typ e (Srt set) T -> T = (Srt kind).
intros.
apply typ_inversion with e (Srt set) T; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_ref :
   forall (P : Prop) e T n,
   typ e (Ref n) T ->
   (forall s, e |- T : Srt s -> forall U : term, item _ U e n -> e |- T >> (lift (S n) U) : s -> P) -> P.
intros.
apply typ_inversion with e (Ref n) T; simpl in |- *; intros;
 auto with coc core arith datatypes.
apply H0 with s x; auto with coc core arith datatypes.
apply (coerce_sort_l H2).
Qed.

  Lemma inv_typ_abs :
   forall (P : Prop) e A M (U : term),
   typ e (Abs A M) U ->
   (forall s, e |- U : Srt s ->
    forall s1 T,
    typ e A (Srt s1) ->
    typ (A :: e) M T -> 
    typ (A :: e) T (Srt s) ->
    e |- (Prod A T) >> U : s -> P) ->
   P.
intros.
apply typ_inversion with e (Abs A M) U; simpl in |- *;
 auto with coc core arith datatypes; intros.

pose (coerce_sym H3).
apply H0 with s s1 U0; auto with coc core arith datatypes.
apply (coerce_sort_l H3).
pose (coerce_sort_r H3).
destruct (generation_prod2 t).
assumption.
Qed.

Lemma inv_typ_abs2 :
   forall (P : Prop) e A M (U : term),
   typ e (Abs A M) U ->
   (forall s, e |- U : Srt s ->
    forall s1 T,
    typ e A (Srt s1) ->
    typ (A :: e) M T -> 
    typ (A :: e) T (Srt s) ->
    e |- (Prod A T) >> U : s -> P) ->
   P.
intros.
apply typ_inversion with e (Abs A M) U; simpl in |- *;
 auto with coc core arith datatypes; intros.

pose (coerce_sym H3).
apply H0 with s s1 U0; auto with coc core arith datatypes.
apply (coerce_sort_l H3).
pose (coerce_sort_r H3).
destruct (generation_prod2 t).
assumption.
Qed.

Lemma inv_typ_app :
 forall (P : Prop) e u v T,
 typ e (App u v) T ->
 (forall s, e |- T : Srt s ->
 forall V Ur : term,
 typ e u (Prod V Ur) -> typ e v V -> coerce e T (subst v Ur) s -> P) -> P.
intros.
apply typ_inversion with e (App u v) T; simpl in |- *;
 auto with coc core arith datatypes; intros.

apply H0 with s V Ur; auto with coc core arith datatypes.
apply (coerce_sort_l H3).
Qed.

  Lemma inv_typ_pair :
   forall (P : Prop) e T u v T',
   typ e (Pair T u v) T' ->
   (forall s, e |- T' : Srt s ->
     forall T U V : term, forall s1,
     typ e U (Srt s1) ->
     typ e u U -> typ (U :: e) V (Srt s) -> typ e v (subst u V) ->
     T = (Sum U V) -> coerce e T' (Sum U V) s -> P) -> P.
intros.
apply typ_inversion with e (Pair T u v) T'; simpl in |- *;
 auto with coc core arith datatypes; intros.

apply H0 with s T U V s1 ; auto with coc core arith datatypes.

apply (coerce_sort_l H5).
pose (coerce_sort_r H5).
destruct (generation_sum2 t).
intuition.
Qed.


  Lemma inv_typ_prod :
   forall (P : Prop) e T (U s : term),
   typ e (Prod T U) s ->
   (forall s1 s2,
    typ e T (Srt s1) -> typ (T :: e) U (Srt s2) -> 
    (s2 = kind \/ coerce e (Srt s2) s kind) -> P) -> P.
intros.
apply typ_inversion with e (Prod T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.

apply H0 with s1 s2; auto with coc core arith datatypes.
destruct H3.
left.
rewrite H3 in H.
destruct (generation_prod2 H).
exact (unique_sort H2 H5).

right.
exact (coerce_sym H3).
Qed.

Lemma inv_typ_prod2 :
   forall (P : Prop) e T (U s : term),
   typ e (Prod T U) s ->
   (forall s1,
    typ e T (Srt s1) -> typ (T :: e) U s -> P) -> P.
intros.
apply typ_inversion with e (Prod T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.

apply H0 with s1; auto with coc core arith datatypes.
induction H3.
rewrite H3 in H.
destruct (generation_prod2 H).
rewrite H3 ; auto.

pose (coerce_propset_r H3).
rewrite e0.
assumption.
Qed.

Lemma inv_typ_sum2 :
   forall (P : Prop) e T (U s : term),
   typ e (Sum T U) s ->
   (typ e T s -> typ (T :: e) U s -> P) -> P.
intros.
apply typ_inversion with e (Sum T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.
inversion H3 ; intuition.
pose (coerce_propset_r H4).
rewrite H8 in e0.
rewrite e0 in H0.
rewrite H6 in H1.
rewrite H5 in H2.
apply H0 ; auto.
pose (coerce_propset_r H4).
rewrite H8 in e0.
rewrite e0 in H0.
rewrite H6 in H1.
rewrite H5 in H2.
apply H0 ; auto.
Qed.

  Lemma inv_typ_subset :
   forall (P : Prop) e T (U s : term),
   typ e (Subset T U) s ->
   (typ e T (Srt set) -> typ (T :: e) U (Srt prop) -> coerce e (Srt set) s kind -> P) -> P.
intros.
apply typ_inversion with e (Subset T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.

rewrite H1 in H3.
rewrite H2 in H4.
apply H0 ; auto.
rewrite H1 in H5.
exact (coerce_sym H5).
Qed.

Lemma inv_typ_pi1 : 
  forall (P : Prop) e t T,
   typ e (Pi1 t) T ->
   (forall s, typ e T (Srt s) ->
   forall U V, typ e t (Sum U V) -> 
   coerce e U T s -> P) -> P.
Proof.
intros.
apply typ_inversion with e (Pi1 t) T; simpl in |- *;
 auto with coc core arith datatypes; intros.

apply H0 with s U V ; auto with coc.
exact (coerce_sort_l H2).
Qed.

Lemma inv_typ_pi2 : 
  forall (P : Prop) e t T,
   typ e (Pi2 t) T ->
   (forall s, typ e T (Srt s) -> forall U V, typ e t (Sum U V) ->  coerce e (subst (Pi1 t) V) T s -> P) -> P.
Proof.
intros.
apply typ_inversion with e (Pi2 t) T; simpl in |- *;
 auto with coc core arith datatypes; intros.

apply H0 with s U V ; auto with coc.
exact (coerce_sort_l H2).
Qed.

Lemma typ_mem_kind : forall e t T, mem_sort kind t -> ~ typ e t T.
red in |- * ; intros.

apply typ_inversion with e t T; auto with coc core arith datatypes.
generalize e T.
clear H0.
elim H; simpl in |- * ; auto with coc core arith datatypes; intros.
apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

apply typ_inversion with (u :: e0) v (Srt s2);
 auto with coc core arith datatypes.

apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.



apply typ_inversion with (u :: e0) v U; auto with coc core arith datatypes.

apply typ_inversion with e0 u (Prod V Ur); auto with coc core arith datatypes.

apply typ_inversion with e0 v V; auto with coc core arith datatypes.

pose (coerce_sort_r H6).
rewrite <- H5 in t0.

apply typ_inversion with e0 T0 (Srt s); auto with coc core arith datatypes.

apply typ_inversion with e0 u U; auto with coc core arith datatypes.
apply typ_inversion with e0 v (subst u V); auto with coc core arith datatypes.

apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

apply typ_inversion with (u :: e0) v (Srt s2); auto with coc core arith datatypes.

rewrite H2 in H4.
apply typ_inversion with e0 u (Srt set); auto with coc core arith datatypes.

rewrite H3 in H5.
apply typ_inversion with (u :: e0) v (Srt prop); auto with coc core arith datatypes.

apply typ_inversion with e0 u (Sum U V); auto with coc core arith datatypes.

apply typ_inversion with (e0) u (Sum U V); auto with coc core arith datatypes.
Qed.

Lemma inv_typ_conv_kind : forall e t T, conv t (Srt kind) -> ~ typ e t T.
intros.
apply typ_mem_kind.
apply red_sort_mem.
elim church_rosser with t (Srt kind); intros;
 auto with coc core arith datatypes.
rewrite (red_normal (Srt kind) x); auto with coc core arith datatypes.
red in |- *; red in |- *; intros.
inversion_clear H2.
Qed.
