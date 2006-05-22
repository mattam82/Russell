Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import CCSum.Types.
Require Import CCSum.Inversion.
Require Import CCSum.Thinning.
Require Import CCSum.Substitution.
Require Import CCSum.TypeCase.
Require Import CCSum.SubjectLambda.Reduction.


Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

  Theorem typ_unique :
   forall e t T, typ e t T -> (forall U : term, typ e t U -> conv T U).
induction 1 ; intros ; auto with coc core arith datatypes.

apply sym_conv.
apply inv_typ_prop with e; auto with coc core arith datatypes.

apply sym_conv.
apply inv_typ_set with e; auto with coc core arith datatypes.

apply inv_typ_ref with e U v; auto with coc core arith datatypes; intros.
elim H0; intros.
rewrite H4.
elim fun_item with term U0 x e v; auto with coc core arith datatypes.

apply inv_typ_abs with e T M U0; auto with coc core arith datatypes; intros.
apply trans_conv_conv with (Prod T T0); auto with coc core arith datatypes.

apply inv_typ_app with e u v U; auto with coc core arith datatypes; intros.
apply trans_conv_conv with (subst v Ur0); auto with coc core arith datatypes.
unfold subst in |- *; apply conv_conv_subst;
 auto with coc core arith datatypes.
apply inv_conv_prod_r with V V0; auto with coc core arith datatypes.

apply sym_conv.
apply type_pair_unique with e (Pair (Sum U V) u v) u v ; auto with coc core arith datatypes.

apply inv_typ_prod with e T U U0; auto with coc core arith datatypes;
 intros.
apply trans_conv_conv with (Srt s3); auto with coc core arith datatypes.

apply inv_typ_sum with e T U U0; auto with coc core arith datatypes;
 intros.
apply trans_conv_conv with (Srt s3); auto with coc core arith datatypes.

apply inv_typ_subset with e T U U0; auto with coc core arith datatypes;
 intros.

apply inv_typ_pi1 with e t U0; auto with coc core arith datatypes;
 intros.
apply trans_conv_conv with U1; auto with coc core arith datatypes.
pose (IHtyp _ H1).
apply (inv_conv_sum_l _ _ _ _ c).


apply inv_typ_pi2 with e t U0; auto with coc core arith datatypes;
 intros.
apply trans_conv_conv with (subst (Pi1 t) V0); auto with coc core arith datatypes.
unfold subst ; apply conv_conv_subst ; auto with coc core arith datatypes.
pose (IHtyp _ H1).
apply (inv_conv_sum_r _ _ _ _ c).

apply inv_typ_let_in with e t v U0; auto with coc core arith datatypes;
 intros.
apply trans_conv_conv with (subst t T'); auto with coc core arith datatypes.
unfold subst ; apply conv_conv_subst ; auto with coc core arith datatypes.
pose (IHtyp1 _ H4).


apply IHtyp3.
apply typ_conv_env with (V :: e) ; auto with coc core arith.
apply (typ_wf _ _ _ H1).

apply trans_conv_conv with U; auto with coc core arith datatypes.
Qed.


  Lemma type_kind_not_conv :
   forall e t T, typ e t T -> typ e t (Srt kind) -> T = Srt kind.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
elim H1; intros.
elim inv_typ_conv_kind with e T (Srt x); auto with coc core arith datatypes.
apply typ_unique with e t; auto with coc core arith datatypes.
Qed.

  Lemma type_reduction :
   forall e t T (U : term), red T U -> typ e t T -> typ e t U.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
inversion_clear H1.
apply type_conv with T x; auto with coc core arith datatypes.
apply subject_reduction with T; auto with coc core arith datatypes.

elim red_normal with T U; auto with coc core arith datatypes.
rewrite H1.
red in |- *; red in |- *; intros.
inversion_clear H2.
Qed.



  Lemma typ_conv_conv :
   forall e u (U : term) v (V : term),
   typ e u U -> typ e v V -> conv u v -> conv U V.
intros.
elim church_rosser with u v; auto with coc core arith datatypes; intros.
apply typ_unique with e x.
apply subject_reduction with u; auto with coc core arith datatypes.

apply subject_reduction with v; auto with coc core arith datatypes.
Qed.
