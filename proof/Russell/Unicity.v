Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Env.

Require Import Russell.Types.
Require Import Russell.Coercion.
Require Import Russell.Inversion.
Require Import Russell.Thinning.
Require Import Russell.Substitution.
Require Import Russell.TypeCase.
Require Import Russell.Generation.
Require Import Russell.GenerationCoerce.
Require Import Russell.UnicityOfSorting.
Require Import Russell.Transitivity.
Require Import Russell.SubjectReduction.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Lemma type_pair_unique : forall e t T, e |- t : T -> 
    forall U V u v, t = (Pair (Sum U V) u v) -> exists s, e |- (Sum U V) >> T : s.
Proof.
intros ; induction H ; try discriminate.
injection H0 ; intros.
rewrite <- H7 ; rewrite <- H8.
exists s3.
apply coerce_refl.
apply type_sum with s1 s2 ; auto with coc.

pose (IHtyp1 H0).
destruct e0.
pose (coerce_sort_r H4).
pose (coerce_sort_l H3).
exists s.
apply coerce_trans with U0; auto with coc core arith datatypes.
rewrite (unique_sort t1 t0) ; assumption.
Qed.

Lemma type_pair_unique2 : forall e t T, typ e t T ->
   forall T' u v, t = (Pair T' u v) -> exists U,  exists  V, T' = Sum U V.
Proof.
intros ; induction H ; try discriminate.
injection H0 ; intros.
exists U ; exists V.
auto with coc.

induction (IHtyp1 H0).
induction H4.
exists x ; exists x0.
apply H4.
Qed.

Theorem typ_unique : forall e t T, typ e t T -> (forall U : term, typ e t U -> 
  ((U = Srt kind) \/ (exists s, e |- T >> U : s))).
induction 1 ; intros ; auto with coc core arith datatypes.

elim inv_typ_prop with e U; auto with coc core arith datatypes.

elim inv_typ_set with e U; auto with coc core arith datatypes.

right.
apply inv_typ_ref with e U n; auto with coc core arith datatypes; intros.
elim H0; intros.
rewrite H5.
elim fun_item with term U0 x e n; auto with coc core arith datatypes.
exists s ; auto with coc.

apply inv_typ_abs with e T M U0; auto with coc core arith datatypes; intros.
right.
exists s.
apply coerce_trans with (Prod T T0); auto with coc core arith datatypes.
pose (IHtyp3 _ H5).
destruct o.
elim typ_not_kind with (T :: e) T0 (Srt s) ; auto with coc.
destruct H8.
pose (coerce_sort_r H8).
pose (unique_sort t H6).
rewrite <- e0.
apply coerce_prod with s0 ; auto with coc.
apply (coerce_sort_l H8).

apply inv_typ_app with e u v U; auto with coc core arith datatypes; intros.
right.
destruct (IHtyp2 _ H3).
intuition ; discriminate.
destruct H6.
exists s.
apply coerce_trans with (subst v Ur0); auto with coc core arith datatypes.
apply substitution_coerce with V0;
 auto with coc core arith datatypes.
pose (inv_sub_prod_r H6); auto with coc core arith datatypes.
pose (inv_sub_prod_l H6); auto with coc core arith datatypes.
destruct e0.
pose (coerce_sort_r c).
assert(V :: e |- Ur0 : Srt x).
apply typ_conv_env with (V0 :: e) ; auto with coc.
apply coerce_env_hd with x0 ; auto with coc.
apply wf_var with x0 ; auto with coc.
apply (coerce_sort_r H7).
pose (substitution H8 H).
change (subst v (Srt x)) with (Srt x) in t0.
pose (coerce_sort_r H5).
pose (unique_sort t0 t1).
rewrite <- e0 ; auto.

right.
apply type_pair_unique with (Pair (Sum U V) u v) u v ; auto with coc core arith datatypes.

apply inv_typ_prod with e T U U0; auto with coc core arith datatypes;
 intros.
pose (generation_prod H1).
destruct e0.
rewrite H5 in H1.
pose (generation_prod2 H1).
destruct a.
destruct H6.
pose (unique_sort H3 H7).
pose (unique_sort H3 H0).
destruct H4.
rewrite <- e0 in H5.
rewrite H4 in H5 ; left ; assumption.
right.
exists kind.
rewrite <- e1 ; assumption.

apply inv_typ_sum2 with e T U U0; auto with coc core arith datatypes;
 intros.
destruct (IHtyp2 _ H4).
left ; auto.
destruct H5.
pose (generation_sum H2).
destruct e0.
rewrite H6 in H2.
pose (generation_sum2 H2).
destruct a.
destruct H8.
rewrite H6.
pose (unique_sort H0 H8).
right ; exists kind.
rewrite <- e0.
pose (typ_wf H7).
induction H1 ; intuition ;
rewrite H1 ; rewrite H12 ;
apply coerce_refl ; auto with coc.

apply inv_typ_subset with e T U U0; auto with coc core arith datatypes;
 intros.
right.
exists kind ; auto.

apply inv_typ_pi1 with e t U0; auto with coc core arith datatypes;
 intros.
right.
exists s.
destruct (IHtyp _ H2) ; try discriminate.
destruct H4.
apply coerce_trans with U1 ; auto with coc.
pose (inv_sub_sum_l H4).
apply any_sort_coerce_l with x ; auto with coc.
pose (unique_sort (coerce_sort_l H3) (coerce_sort_r c)).
rewrite e0 ; auto.
apply (coerce_sort_l c).

apply inv_typ_pi2 with e t U0; auto with coc core arith datatypes;
 intros.
right.
exists s.
destruct (IHtyp _ H2) ; try discriminate.
destruct H4.
apply coerce_trans with (subst (Pi1 t) V0) ; auto with coc.
pose (inv_sub_sum_r H4).
assert(e |- Pi1 t : U) by apply type_pi1 with V ; auto.
apply substitution_coerce with U ; auto.
pose (coerce_sort_r c).
pose (substitution t0 H5).
change (subst (Pi1 t) (Srt x)) with (Srt x) in t1.
pose (coerce_sort_l H3).
pose (unique_sort t1 t2).
rewrite <- e0 ; auto.

pose (IHtyp1 _ H3).
destruct o.
left ; auto.
right.
destruct H4.
exists x ; apply coerce_trans with U ; auto.
rewrite <- (unique_sort (coerce_sort_l H2) (coerce_sort_l H4)).
apply coerce_sym ; auto.
Qed.

  Lemma type_kind_not_conv :
   forall e t T, typ e t T -> typ e t (Srt kind) -> T = Srt kind.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
elim H1; intros.
elim inv_typ_conv_kind with e T (Srt x); auto with coc core arith datatypes.
elim (typ_unique H0 H) ; auto with coc.
intros.
rewrite H3 ; auto with coc.
intros.
destruct H3.
pose (coerce_sort_l H3).
elim typ_not_kind with e (Srt kind) (Srt x0) ; auto.
Qed.

  Lemma type_reduction :
   forall e t T (U : term), red T U -> typ e t T -> typ e t U.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
inversion_clear H1.
assert(e |- U : Srt x).
apply subject_reduction with T; auto with coc core arith datatypes.
apply type_conv with T x; auto with coc core arith datatypes.

elim red_normal with T U; auto with coc core arith datatypes.
rewrite H1.
red in |- *; red in |- *; intros.
inversion_clear H2.
Qed.

Lemma typ_conv_conv_coerce : forall e u (U : term) v (V : term), 
  e |- u : U -> e |- v : V -> conv u v -> 
  (U = V \/ exists s, e |- U >> V : s).
Proof.
intros.
elim church_rosser with u v; auto with coc core arith datatypes; intros.
pose (subject_reduction H2 H).
pose (subject_reduction H3 H0).
pose (typ_unique t t0).
destruct o.
rewrite H4 in t0.
pose (typ_unique t0 t).
destruct o.
rewrite H4 ; rewrite H5 ; left ; auto.
destruct H5.
pose (coerce_sort_l H5).
elim typ_not_kind with e (Srt kind) (Srt x0) ; auto.
destruct H4.
right.
exists x0 ; auto.
Qed.


