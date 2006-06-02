Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.CCSum.Types.
Require Import Lambda.CCSum.Inversion.
Require Import Lambda.CCSum.Thinning.
Require Import Lambda.CCSum.Substitution.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

  Theorem type_case :
   forall e t T,
   typ e t T -> (exists s : sort, typ e T (Srt s)) \/ T = Srt kind.
simple induction 1; intros; auto with coc core arith datatypes.
left.
elim wf_sort_lift with v e0 t0; auto with coc core arith datatypes; intros.
exists x; auto with coc core arith datatypes.

left.
exists s2.
apply type_prod with s1; auto with coc core arith datatypes.

left.
elim H3; intros.
elim H4; intros.
apply inv_typ_prod with e0 V Ur (Srt x); auto with coc core arith datatypes;
 intros.
exists s2.
replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

discriminate H4.

left.
exists s2.
apply type_sum with s1 ; auto with coc core arith datatypes.

case s2; auto with coc core arith datatypes.
left.
exists kind.
apply type_prop.
apply typ_wf with T0 (Srt s1); auto with coc core arith datatypes.

left.
exists kind.
apply type_set.
apply typ_wf with T0 (Srt s1); auto with coc core arith datatypes.

case s2.
right ; auto.
left.
exists kind ; apply type_prop.
apply typ_wf with T0 (Srt s1); auto with coc core arith datatypes.

left; exists kind ; apply type_set.
apply typ_wf with T0 (Srt s1); auto with coc core arith datatypes.

induction H1.
induction H1.
apply inv_typ_sum with e0 U V (Srt x) ; auto with coc core arith.
intros.
left ; exists s1 ; auto with coc core arith.
discriminate H1.

induction H1.
left.
induction H1.
exists x ; auto with coc core.
replace (Srt x) with (subst (Pi1 t0) (Srt x)).
apply substitution with U ; auto with coc core.
apply inv_typ_sum with e0 U V (Srt x) ; auto with coc core arith.
intros.
rewrite <- (conv_sort _ _ H4).
assumption.
apply type_pi1 with V ; auto with coc core arith datatypes.
unfold subst ; simpl ; auto.
discriminate H1.

induction H4.
left ; exists s ; auto.
left.
exists s ; auto.
Qed.

  Lemma type_free_db : forall e t T, typ e t T -> free_db (length e) T.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
inversion_clear H0.
apply typ_free_db with (Srt x); auto with coc core arith datatypes.

rewrite H0; auto with coc core arith datatypes.
Qed.
