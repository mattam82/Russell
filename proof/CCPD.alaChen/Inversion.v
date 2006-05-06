Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Substitution.
Require Import CCPD.Coercion.
Require Import CCPD.Generation.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.



  Definition inv_type (P : Prop) e t T s : Prop :=
    match t with
    | Srt prop => T = (Srt kind) -> P
    | Srt set => T = (Srt kind) -> P
    | Srt kind => True
    | Ref n => forall x : term, item _ x e n -> 
       e |- T : Srt s -> e |- T >> (lift (S n) x) : s -> P
    | Abs A M =>
        forall s1 (U : term),
        typ e A (Srt s1) ->
        typ (A :: e) M U -> coerce e T (Prod A U) s -> P
    | App u v =>
        forall Ur V : term,
        typ e v V -> typ e u (Prod V Ur) -> 
        typ e T (Srt s) ->
        coerce e T (subst v Ur) s -> P
    | Pair T' u v => 
        forall U s1, typ e U (Srt s1) ->
	  typ e u U -> 
	  forall V, typ e v (subst u V) -> T' = (Sum U V) -> coerce e T (Sum U V) s -> P
    | Prod A B =>
        forall s1 s2,
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) -> s = kind -> coerce e T (Srt s2) s -> P
    | Sum A B =>
        forall s1 s2,
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) -> s = kind -> coerce e T (Srt s2) s -> P
    | Subset A B =>
        typ e A (Srt set) -> typ (A :: e) B (Srt prop) -> s = kind -> coerce e T (Srt set) s -> P
    | Pi1 t =>
        forall U V,
        typ e t (Sum U V) -> 
        coerce e T U s -> P
    | Pi2 t =>
        forall U V,
        typ e t (Sum U V) -> 
        coerce e T (subst (Pi1 t) V) s -> P
    | Let_in t v =>
        forall U, typ e t U -> 
	forall s1, typ e U (Srt s1) ->
        forall M, typ (U :: e) v M -> 
        coerce e T (subst t M) s -> P
    end.
    (*
Lemma coerce_not_kind : forall e T U, e |- T >> U ->
   forall s, e |- T : (Srt s) -> e |- U : Srt s
    -> (T <> (Srt kind) /\ U <> Srt kind).
Proof.
  induction 1 ; intros ; try solve [ split ; red ; intros ; discriminate ].
   
  split.
  apply typ_not_kind with e (Srt s) ; auto.
  apply typ_not_kind with e (Srt s) ; auto.

  split.
  red ; intros ; discriminate.
  apply typ_not_kind with G (Srt s) ; auto.

  split.
  apply typ_not_kind with G (Srt s) ; auto.

  red ; intros ; discriminate.

  destruct (IHcoerce1 s H H0).
  destruct (IHcoerce2 s H0 H1).
  auto.
Qed.

Lemma unicity_sorting : forall e t s1, e |- t : Srt s1 -> forall s2,
  e |- t : Srt s2 -> s1 = s2.
Admitted.

Lemma conv_sorting : forall e T U, conv T U -> 
  forall s1, e |- T : Srt s1 -> 
  forall s2, e |- U : Srt s2 -> s1 = s2.
Admitted.


Lemma coerce_sorts : forall e T U, e |- T >> U ->
 forall s1, e |- T : Srt s1 -> forall s2, e |- U : Srt s2 ->
 s1 = s2.
Proof.
  induction 1 ; intros.
  apply conv_sorting with G A B ; auto.

  apply IHcoerce2.
  inversion H3.
  pose (conv_in_env).

  pose (IHcoerce1 s H s
  *)
  
  

Lemma typ_not_kind : forall G t T, G |- t : T -> t <> Srt kind.
Proof.
  induction 1 ; intros ; unfold not ; intros ; try discriminate ; auto with coc.
Qed.
  
Lemma inv_type_coerce : forall (P : Prop) e t (U V : term) s,
  inv_type P e t U s -> coerce e U V s -> inv_type P e t V s.
intros P e.
induction t ; simpl in |- *; intros U V s' H Hco ; intros.
destruct (coerce_sort e _ _ s' Hco).
generalize H ; clear H.
elim s; auto with coc core arith datatypes; intros ;
rewrite H2 in H1 ; elim (typ_not_kind _ _ _ H1) ; auto.

apply H with x ; auto with coc core arith datatypes.
eapply coerce_sort_l with V ; auto with coc core.
eapply coerce_trans with V ; auto with coc core.

apply H with s1 U0; auto with coc core arith datatypes.
eapply coerce_trans with V ; auto with coc core.

apply H with Ur V0; auto with coc core arith datatypes.
eapply coerce_sort_l with V ; auto with coc core.
eapply coerce_trans with V ; auto with coc core.

apply H with U0 s1 V0 ; auto with coc core arith datatypes.
eapply coerce_trans with V ; auto with coc core.

apply H with s1 s2; auto with coc core arith datatypes.
eapply coerce_trans with V ; auto with coc core.

apply H with s1 s2; auto with coc core arith datatypes.
eapply coerce_trans with V ; auto with coc core.

apply H ; auto with coc core arith datatypes.
eapply coerce_trans with V ; auto with coc core.

apply H with U0 V0; auto with coc core arith datatypes.
eapply coerce_trans with V ; auto with coc core.

apply H with U0 V0; auto with coc core arith datatypes.
eapply coerce_trans with V ; auto with coc core.

apply H with U0 s1 M; auto with coc core arith datatypes.
eapply coerce_trans with V ; auto with coc core.
Qed.

Lemma inv_type_sort : forall P e t V s, 
  e |- V : Srt s -> inv_type P e t V s -> 
  forall s', e |- V : Srt s' -> inv_type P e t V s'.
Proof.
  induction t; simpl ; intros ; auto with coc.
  apply H0 with x ; auto with coc core arith.
  





  Theorem typ_inversion :
   forall (P : Prop) e t T, typ e t T -> forall s, typ e T (Srt s) -> inv_type P e t T s -> P.
induction 1; simpl in |- *; intros.
auto with coc core arith datatypes.

auto with coc core arith datatypes.

elim H0; intros.
apply H2 with x; auto with coc core arith datatypes.
rewrite H3.
apply coerce_refl ; auto with coc core.
rewrite <- H3 ; auto.

apply H3 with s1 U; auto with coc core arith datatypes.

apply H2 with Ur V; auto with coc core arith datatypes.

apply H4 with U s1 V; auto with coc core arith datatypes.

apply H2 with s1 s2; auto with coc core arith datatypes.
apply (typ_sort_kind _ _ _ H1).

apply H2 with s1 s2; auto with coc core arith datatypes.
apply (typ_sort_kind _ _ _ H1).

apply H2; auto with coc core arith datatypes.
apply (typ_sort_kind _ _ _ H1).

apply H1 with U V; auto with coc core arith datatypes.

apply H1 with U V; auto with coc core arith datatypes.

apply H4 with U s1 M; auto with coc core arith datatypes.

pose (coerce_sym _ _ _ _ H2).
apply IHtyp1 with s ; auto with coc core arith.
pose (inv_type_coerce).
cut (inv_type P e t V s).
intro invt.
apply (inv_type_coerce P e t V U s invt c).



Qed.



  Lemma inv_typ_kind : forall e t, ~ typ e (Srt kind) t.
red in |- *; intros.
apply typ_inversion with e (Srt kind) t; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_prop : forall e T, typ e (Srt prop) T -> coerce e T (Srt kind).
intros.
apply typ_inversion with e (Srt prop) T; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_set : forall e T, typ e (Srt set) T -> coerce e T (Srt kind).
intros.
apply typ_inversion with e (Srt set) T; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_ref :
   forall (P : Prop) e T n,
   typ e (Ref n) T ->
   (forall U : term, item _ U e n -> coerce e T (lift (S n) U) -> P) -> P.
intros.
apply typ_inversion with e (Ref n) T; simpl in |- *; intros;
 auto with coc core arith datatypes.
apply H0 with x; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_abs :
   forall (P : Prop) e A M (U : term),
   typ e (Abs A M) U ->
   (forall s1 s2 T,
    typ e A (Srt s1) ->
    typ (A :: e) M T -> typ (A :: e) T (Srt s2) -> coerce e (Prod A T) U -> P) ->
   P.
intros.
apply typ_inversion with e (Abs A M) U; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with s1 s2 U0; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_app :
   forall (P : Prop) e u v T,
   typ e (App u v) T ->
   (forall V Ur : term,
    typ e u (Prod V Ur) -> typ e v V -> coerce e T (subst v Ur) -> P) -> P.
intros.
apply typ_inversion with e (App u v) T; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with V Ur; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_pair :
   forall (P : Prop) e T u v T',
   typ e (Pair T u v) T' ->
   (forall T U V : term, forall s1 s2,
     typ e U (Srt s1) ->
     typ e u U -> typ (U :: e) V (Srt s2) -> typ e v (subst u V) ->
     T = (Sum U V) -> coerce e T' (Sum U V) -> P) -> P.
intros.
apply typ_inversion with e (Pair T u v) T'; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with T U V s1 s2 ; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_prod :
   forall (P : Prop) e T (U s : term),
   typ e (Prod T U) s ->
   (forall s1 s2,
    typ e T (Srt s1) -> typ (T :: e) U (Srt s2) -> coerce e (Srt s2) s -> P) -> P.
intros.
apply typ_inversion with e (Prod T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with s1 s2; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_sum :
   forall (P : Prop) e T (U s : term),
   typ e (Sum T U) s ->
   (forall s1 s2,
    typ e T (Srt s1) -> typ (T :: e) U (Srt s2) -> coerce e (Srt s2) s -> P) -> P.
intros.
apply typ_inversion with e (Sum T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with s1 s2; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_subset :
   forall (P : Prop) e T (U s : term),
   typ e (Subset T U) s ->
   (typ e T (Srt set) -> typ (T :: e) U (Srt prop) -> coerce e (Srt set) s -> P) -> P.
intros.
apply typ_inversion with e (Subset T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.
Qed.

Lemma inv_typ_pi1 : 
  forall (P : Prop) e t T,
   typ e (Pi1 t) T ->
   (forall U V, typ e t (Sum U V) ->  coerce e U T -> P) -> P.
Proof.
intros.
apply typ_inversion with e (Pi1 t) T; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with U V ; auto with coc.
Qed.

Lemma inv_typ_pi2 : 
  forall (P : Prop) e t T,
   typ e (Pi2 t) T ->
   (forall U V, typ e t (Sum U V) ->  coerce e (subst (Pi1 t) V) T -> P) -> P.
Proof.
intros.
apply typ_inversion with e (Pi2 t) T; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with U V ; auto with coc.
Qed.

Lemma inv_typ_let_in : 
  forall (P : Prop) e v t T,
   typ e (Let_in v t) T ->
   (forall V, typ e v V -> 
   forall s1, typ e V (Srt s1) ->
   forall T', typ (V :: e) t T' ->
   forall s2, typ (V :: e) T' (Srt s2) ->
   coerce e (subst v T')  T -> P) -> P.
Proof.
intros.
apply typ_inversion with e (Let_in v t) T; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply (H0 U H1 s1 H2 M H3 s2 H4) ; auto with coc.
Qed.


  Lemma typ_mem_kind : forall e t T, mem_sort kind t -> ~ typ e t T.
red in |- *; intros.
apply typ_inversion with e t T; auto with coc core arith datatypes.
generalize e T.
clear H0.
elim H; simpl in |- *; auto with coc core arith datatypes; intros.
apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

apply typ_inversion with (u :: e0) v (Srt s2);
 auto with coc core arith datatypes.

apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

apply typ_inversion with (u :: e0) v U; auto with coc core arith datatypes.

apply typ_inversion with e0 u (Prod V Ur); auto with coc core arith datatypes.

apply typ_inversion with e0 v V; auto with coc core arith datatypes.

rewrite H6 in H0.
rewrite H6 in H1.
simpl in H1.
apply H1 with e0 (Srt s2) s1 s2 ;  auto with coc core arith datatypes.
apply typ_inversion with e0 u U; auto with coc core arith datatypes.
apply typ_inversion with e0 v (subst u V); auto with coc core arith datatypes.

apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

apply typ_inversion with (u :: e0) v (Srt s2); auto with coc core arith datatypes.

apply typ_inversion with e0 u (Srt set); auto with coc core arith datatypes.

apply typ_inversion with (u :: e0) v (Srt prop); auto with coc core arith datatypes.

apply typ_inversion with e0 u (Sum U V); auto with coc core arith datatypes.

apply typ_inversion with (e0) u (Sum U V); auto with coc core arith datatypes.

apply typ_inversion with e0 u U; auto with coc core arith datatypes.

apply typ_inversion with (U :: e0) v M; auto with coc core arith datatypes.
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

Lemma type_pair_unique : forall e t T, typ e t T -> forall U V u v, t = (Pair (Sum U V) u v) ->
   coerce e T (Sum U V).
Proof.
intros ; induction H ; try discriminate.
injection H0 ; intros.
rewrite H6 ; rewrite H7.
apply refl_coerce.
pose (IHtyp1 H0).
apply coerce_trans with U0; auto with coc core arith datatypes.
Qed.

Lemma type_pair_unique2 : forall e t T, typ e t T -> 
   forall T' u v, t = (Pair T' u v) -> exists U,  exists  V, T' = Sum U V /\ 
   coerce e T (Sum U V).
Proof.
intros ; induction H ; try discriminate.
injection H0 ; intros.
exists U ; exists V.
split ; auto with coc.

induction (IHtyp1 H0).
induction H3.
induction H3.
exists x ; exists x0.
split ; auto with coc.
apply coerce_trans with U; auto with coc core arith datatypes.
Qed.
