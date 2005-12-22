Require Import Termes.
Require Import Reduction.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.


  Lemma typ_sub_weak :
   forall g (d : term) t,
   typ g d t ->
   forall e u (U : term),
   typ e u U ->
   forall f n,
   sub_in_env d t n e f ->
   wf f -> trunc _ n f g -> typ f (subst_rec d u n) (subst_rec d U n).
intros g d t H.
intros e u U H0.
induction H0 using typ_mut with
 (P := fun e u (U : term) => fun H0 : e |- u : U =>
 forall f n,
 sub_in_env d t n e f ->
 wf f -> trunc term n f g -> f |- subst_rec d u n : subst_rec d U n)
 (P0 :=
 fun e T (U : term) => fun H0 : e |- T >> U =>
 forall f n,
 sub_in_env d t n e f ->
 wf f -> trunc term n f g -> f |- subst_rec d T n >> subst_rec d U n) ;
 simpl in |- *;
 try simpl in IHtyp ; 
 try simpl in IHtyp1 ;
 try simpl in IHtyp2 ;
 try simpl in IHtyp3 ; 
 try simpl in IHtyp4 ; intros; auto with coc core arith datatypes.

elim (lt_eq_lt_dec n0 n); [ intro Hlt_eq | intro Hlt ].
elim i.
elim Hlt_eq; clear Hlt_eq.
case n; [ intro Hlt | intros n1 Hlt ]; intros.
inversion_clear Hlt.

simpl in |- *.
rewrite H3.
rewrite simpl_subst; auto with coc core arith datatypes.
apply type_var; auto with coc core arith datatypes.
exists x; auto with coc core arith datatypes.
apply nth_sub_sup with d t n0 e; auto with coc core arith datatypes.

intro Heq; intros.
rewrite H3.
elim Heq.
rewrite simpl_subst; auto with coc core arith datatypes.
replace x with t.
apply thinning_n with g; auto with coc core arith datatypes.

apply fun_item with e n; auto with coc core arith datatypes.
apply nth_sub_eq with d f; auto with coc core arith datatypes.
elim Heq; auto with coc core arith datatypes.

apply type_var; auto with coc core arith datatypes.
apply nth_sub_inf with t e; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

rewrite distr_subst.
apply type_app with (subst_rec d V n); auto with coc core arith datatypes.

apply type_pair with s1 s2 ; auto with coc core arith datatypes.
apply IHtyp3 ; auto with coc.
apply wf_var with s1 ; auto with coc.
rewrite <- distr_subst ; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with (subst_rec d V (S n)) ; auto with coc.

rewrite distr_subst.
simpl.
apply type_pi2 with (subst_rec d U n) ; auto with coc.

cut (wf (subst_rec d U n :: f)).
intro ; rewrite distr_subst.
apply type_let_in with (subst_rec d U n) s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

apply type_conv with (subst_rec d U n) s; auto with coc core arith datatypes.

apply coerce_prod with s ; auto with coc core.

apply IHtyp4 ; auto with coc core.
apply wf_var with s ; auto with coc core.

apply coerce_sum with s ; auto with coc core.

apply IHtyp4 ; auto with coc core.
apply wf_var with s ; auto with coc core.

apply coerce_trans with (subst_rec d B n) s ; auto with coc core.
Qed.

Lemma coerce_sub_weak :
   forall g (d : term) t,
   typ g d t ->
   forall e T (U : term),
   e |- T >> U ->
   forall f n,
   sub_in_env d t n e f ->
   wf f -> trunc _ n f g -> f |- (subst_rec d T n) >> (subst_rec d U n).
intros g d t H.
intros e u U H0.
induction H0 using coerce_mut with
 (P := fun e u (U : term) => fun H0 : e |- u : U =>
 forall f n,
 sub_in_env d t n e f ->
 wf f -> trunc term n f g -> f |- subst_rec d u n : subst_rec d U n)
 (P0 :=
 fun e T (U : term) => fun H0 : e |- T >> U =>
 forall f n,
 sub_in_env d t n e f ->
 wf f -> trunc term n f g -> f |- subst_rec d T n >> subst_rec d U n) ;
 simpl in |- *;
 try simpl in IHcoerce ; 
 try simpl in IHcoerce0 ; 
 try simpl in IHcoerce1 ;
 try simpl in IHcoerce2 ;
 try simpl in IHcoerce3 ; 
 try simpl in IHcoerce4 ; intros; auto with coc core arith datatypes.

elim (lt_eq_lt_dec n0 n); [ intro Hlt_eq | intro Hlt ].
elim i.
elim Hlt_eq; clear Hlt_eq.
case n; [ intro Hlt | intros n1 Hlt ]; intros.
inversion_clear Hlt.

simpl in |- *.
rewrite H3.
rewrite simpl_subst; auto with coc core arith datatypes.
apply type_var; auto with coc core arith datatypes.
exists x; auto with coc core arith datatypes.
apply nth_sub_sup with d t n0 e; auto with coc core arith datatypes.

intro Heq; intros.
rewrite H3.
elim Heq.
rewrite simpl_subst; auto with coc core arith datatypes.
replace x with t.
apply thinning_n with g; auto with coc core arith datatypes.

apply fun_item with e n; auto with coc core arith datatypes.
apply nth_sub_eq with d f; auto with coc core arith datatypes.
elim Heq; auto with coc core arith datatypes.

apply type_var; auto with coc core arith datatypes.
apply nth_sub_inf with t e; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

rewrite distr_subst.
apply type_app with (subst_rec d V n); auto with coc core arith datatypes.

apply type_pair with s1 s2 ; auto with coc core arith datatypes.
apply IHcoerce1 ; auto with coc.
apply wf_var with s1 ; auto with coc.
rewrite <- distr_subst ; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with (subst_rec d V (S n)) ; auto with coc.

rewrite distr_subst.
simpl.
apply type_pi2 with (subst_rec d U n) ; auto with coc.

cut (wf (subst_rec d U n :: f)).
intro ; rewrite distr_subst.
apply type_let_in with (subst_rec d U n) s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

apply type_conv with (subst_rec d U n) s; auto with coc core arith datatypes.

apply coerce_prod with s ; auto with coc core.

apply IHcoerce4 ; auto with coc core.
apply wf_var with s ; auto with coc core.

apply coerce_sum with s ; auto with coc core.

apply IHcoerce4 ; auto with coc core.
apply wf_var with s ; auto with coc core.

apply coerce_trans with (subst_rec d B n) s ; auto with coc core.
Qed.

  Theorem substitution :
   forall e t u (U : term),
   typ (t :: e) u U ->
   forall d : term, typ e d t -> typ e (subst d u) (subst d U).
intros.
unfold subst in |- *.
apply typ_sub_weak with e t (t :: e); auto with coc core arith datatypes.
apply typ_wf with d t; auto with coc core arith datatypes.
Qed.

  Theorem substitution_coerce :
   forall e t T (U : term),
   (t :: e) |- T >> U ->
   forall d : term, e |- d : t -> e |- (subst d T) >> (subst d U).
intros.
unfold subst in |- *.
apply coerce_sub_weak with e t (t :: e); auto with coc core arith datatypes.
apply typ_wf with d t; auto with coc core arith datatypes.
Qed.

Hint Resolve substitution substitution_coerce : coc.

