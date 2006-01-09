Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
v v v v v v v
Require Import Env.
^ ^ ^ ^ ^ ^ ^
Require Import CCP.Types.
Require Import CCP.Coercion.
Require Import CCP.Thinning.
Require Import CCP.Substitution.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
v v v v v v v
Implicit Types e f g : env.
^ ^ ^ ^ ^ ^ ^

  Definition inv_type (P : Prop) e t T : Prop :=
    match t with
v v v v v v v
    | Srt prop => coerce e T (Srt kind) -> P
    | Srt set => coerce e T (Srt kind) -> P
*************
v v v v v v v
    | Srt prop => coerce T (Srt kind) -> P
    | Srt set => coerce T (Srt kind) -> P
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
    | Srt kind => True
    | Ref n => forall x : term, item _ x e n -> coerce e T (lift (S n) x) -> P
    | Abs A M =>
        forall s1 s2 (U : term),
        typ e A (Srt s1) ->
        typ (A :: e) M U -> typ (A :: e) U (Srt s2) -> coerce e T (Prod A U) -> P
    | App u v =>
        forall Ur V : term,
        typ e v V -> typ e u (Prod V Ur) -> coerce e T (subst v Ur) -> P
    | Pair T' u v => 
        forall U s1, typ e U (Srt s1) ->
	  typ e u U -> 
	  forall V s2, typ (U :: e) V (Srt s2) ->
            typ e v (subst u V) -> T' = (Sum U V) -> coerce e T (Sum U V) -> P
    | Prod A B =>
        forall s1 s2,
v v v v v v v
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) -> coerce e T (Srt s2) -> P
*************
v v v v v v v
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) -> coerce T (Srt s2) -> P
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
    | Sum A B =>
        forall s1 s2,
v v v v v v v
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) -> coerce e T (Srt s2) -> P
*************
v v v v v v v
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) -> coerce T (Srt s2) -> P
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
    | Subset A B =>
v v v v v v v
        typ e A (Srt set) -> typ (A :: e) B (Srt prop) -> coerce e T (Srt set) -> P
*************
v v v v v v v
        typ e A (Srt set) -> typ (A :: e) B (Srt prop) -> coerce T (Srt set) -> P
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
    | Pi1 t =>
        forall U V,
        typ e t (Sum U V) -> coerce e T U -> P
    | Pi2 t =>
        forall U V,
        typ e t (Sum U V) -> coerce e T (subst (Pi1 t) V) -> P
    | Let_in t v =>
        forall U, typ e t U -> 
	forall s1, typ e U (Srt s1) ->
        forall M, typ (U :: e) v M -> 
        forall s2, typ (U :: e) M (Srt s2) ->
        coerce e T (subst t M) -> P
    end.
    


  Lemma inv_type_coerce :
   forall (P : Prop) e t (U V : term),
   forall s, e |- U : (Srt s) -> e |- V : (Srt s) ->
   coerce e V U -> inv_type P e t U -> inv_type P e t V.
intros P e t U V UVs Us Vs.
intro.

case t; simpl in |- *; intros.
generalize H0 ; clear H0.
elim s; auto with coc core arith datatypes; intros.

v v v v v v v
apply H1 with x; auto with coc core arith datatypes.
^ ^ ^ ^ ^ ^ ^

v v v v v v v
apply H1 with s1 s2 U0; auto with coc core arith datatypes.
^ ^ ^ ^ ^ ^ ^

apply H1 with Ur V0; auto with coc core arith datatypes.

apply H1 with U0 s1 V0 s2 ; auto with coc core arith datatypes.

apply H1 with s1 s2; auto with coc core arith datatypes.
apply H1 with s1 s2; auto with coc core arith datatypes.
apply H1; auto with coc core arith datatypes.

apply H1 with U0 V0; auto with coc core arith datatypes.

apply H1 with U0 V0; auto with coc core arith datatypes.

apply H1 with U0 s1 M s2; auto with coc core arith datatypes.

intros.
v v v v v v v
induction H ; induction H0 ; auto with coc core.

Admitted.
(*pose coerce_beta.
*************
v v v v v v v
^ ^ ^ ^ ^ ^ ^
apply coerce_trans with V; auto with coc core arith datatypes.
^ ^ ^ ^ ^ ^ ^
Qed.
*)
  Theorem typ_inversion :
   forall (P : Prop) e t T, typ e t T -> inv_type P e t T -> P.
simple induction 1; simpl in |- *; intros.
auto with coc core arith datatypes.

auto with coc core arith datatypes.

elim H1; intros.
apply H2 with x; auto with coc core arith datatypes.
rewrite H3; auto with coc core arith datatypes.

apply H6 with s1 s2 U; auto with coc core arith datatypes.

apply H4 with Ur V; auto with coc core arith datatypes.

apply H8 with U s1 V s2; auto with coc core arith datatypes.

apply H4 with s1 s2; auto with coc core arith datatypes.
apply H4 with s1 s2; auto with coc core arith datatypes.
apply H4; auto with coc core arith datatypes.

apply H2 with U V; auto with coc core arith datatypes.
apply H2 with U V; auto with coc core arith datatypes.

apply H8 with U s1 M s2; auto with coc core arith datatypes.

apply H1.
v v v v v v v
apply inv_type_coerce with V s; auto with coc core arith datatypes.
*************
v v v v v v v
apply inv_type_coerce with V; auto with coc core arith datatypes.
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
Qed.


  Lemma inv_typ_kind : forall e t, ~ typ e (Srt kind) t.
red in |- *; intros.
apply typ_inversion with e (Srt kind) t; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

v v v v v v v
  Lemma inv_typ_prop : forall e T, typ e (Srt prop) T -> coerce e T (Srt kind).
*************
v v v v v v v
  Lemma inv_typ_prop : forall e T, typ e (Srt prop) T -> coerce T (Srt kind).
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
intros.
apply typ_inversion with e (Srt prop) T; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

v v v v v v v
  Lemma inv_typ_set : forall e T, typ e (Srt set) T -> coerce e T (Srt kind).
*************
v v v v v v v
  Lemma inv_typ_set : forall e T, typ e (Srt set) T -> coerce T (Srt kind).
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
intros.
apply typ_inversion with e (Srt set) T; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_ref :
   forall (P : Prop) e T n,
   typ e (Ref n) T ->
v v v v v v v
   (forall U : term, item _ U e n -> coerce e T (lift (S n) U) -> P) -> P.
*************
v v v v v v v
   (forall U : term, item _ U e n -> coerce T (lift (S n) U) -> P) -> P.
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
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
v v v v v v v
    typ (A :: e) M T -> typ (A :: e) T (Srt s2) -> coerce e (Prod A T) U -> P) ->
*************
v v v v v v v
    typ (A :: e) M T -> typ (A :: e) T (Srt s2) -> coerce (Prod A T) U -> P) ->
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
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
v v v v v v v
    typ e u (Prod V Ur) -> typ e v V -> coerce e T (subst v Ur) -> P) -> P.
*************
v v v v v v v
    typ e u (Prod V Ur) -> typ e v V -> coerce T (subst v Ur) -> P) -> P.
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
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
v v v v v v v
     T = (Sum U V) -> coerce e T' (Sum U V) -> P) -> P.
*************
v v v v v v v
     T = (Sum U V) -> coerce T' (Sum U V) -> P) -> P.
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
intros.
apply typ_inversion with e (Pair T u v) T'; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with T U V s1 s2 ; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_prod :
   forall (P : Prop) e T (U s : term),
   typ e (Prod T U) s ->
   (forall s1 s2,
v v v v v v v
    typ e T (Srt s1) -> typ (T :: e) U (Srt s2) -> coerce e (Srt s2) s -> P) -> P.
*************
v v v v v v v
    typ e T (Srt s1) -> typ (T :: e) U (Srt s2) -> coerce (Srt s2) s -> P) -> P.
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
intros.
apply typ_inversion with e (Prod T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with s1 s2; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_sum :
   forall (P : Prop) e T (U s : term),
   typ e (Sum T U) s ->
   (forall s1 s2,
v v v v v v v
    typ e T (Srt s1) -> typ (T :: e) U (Srt s2) -> coerce e (Srt s2) s -> P) -> P.
*************
v v v v v v v
    typ e T (Srt s1) -> typ (T :: e) U (Srt s2) -> coerce (Srt s2) s -> P) -> P.
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
intros.
apply typ_inversion with e (Sum T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with s1 s2; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_subset :
   forall (P : Prop) e T (U s : term),
   typ e (Subset T U) s ->
v v v v v v v
   (typ e T (Srt set) -> typ (T :: e) U (Srt prop) -> coerce e (Srt set) s -> P) -> P.
*************
v v v v v v v
   (typ e T (Srt set) -> typ (T :: e) U (Srt prop) -> coerce (Srt set) s -> P) -> P.
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
intros.
apply typ_inversion with e (Subset T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.
Qed.

Lemma inv_typ_pi1 : 
  forall (P : Prop) e t T,
   typ e (Pi1 t) T ->
v v v v v v v
   (forall U V, typ e t (Sum U V) ->  coerce e U T -> P) -> P.
*************
v v v v v v v
   (forall U V, typ e t (Sum U V) ->  coerce U T -> P) -> P.
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
Proof.
intros.
apply typ_inversion with e (Pi1 t) T; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with U V ; auto with coc.
Qed.

Lemma inv_typ_pi2 : 
  forall (P : Prop) e t T,
   typ e (Pi2 t) T ->
v v v v v v v
   (forall U V, typ e t (Sum U V) ->  coerce e (subst (Pi1 t) V) T -> P) -> P.
*************
v v v v v v v
   (forall U V, typ e t (Sum U V) ->  coerce (subst (Pi1 t) V) T -> P) -> P.
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
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
v v v v v v v
   coerce e (subst v T')  T -> P) -> P.
*************
v v v v v v v
   coerce (subst v T')  T -> P) -> P.
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
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
v v v v v v v
   coerce e T (Sum U V).
*************
v v v v v v v
   coerce T (Sum U V).
^ ^ ^ ^ ^ ^ ^
^ ^ ^ ^ ^ ^ ^
Proof.
intros ; induction H ; try discriminate.
injection H0 ; intros.
rewrite H6 ; rewrite H7.
v v v v v v v
apply refl_coerce.
^ ^ ^ ^ ^ ^ ^
pose (IHtyp1 H0).
v v v v v v v
apply coerce_trans with U0; auto with coc core arith datatypes.
^ ^ ^ ^ ^ ^ ^
Qed.

Lemma type_pair_unique2 : forall e t T, typ e t T -> 
v v v v v v v
   forall T' u v, t = (Pair T' u v) -> exists U,  exists  V, T' = Sum U V /\ 
v v v v v v v
   coerce T (Sum U V).
^ ^ ^ ^ ^ ^ ^
*************
   coerce e T (Sum U V).
^ ^ ^ ^ ^ ^ ^
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
v v v v v v v
apply coerce_trans with U; auto with coc core arith datatypes.
^ ^ ^ ^ ^ ^ ^
Qed.
