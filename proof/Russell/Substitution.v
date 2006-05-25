Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Russell.Types.
Require Import Russell.Thinning.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Lemma double_sub_weak : forall g (d : term) t, g |-- d : t ->
   (forall e u (U : term), e |-- u : U ->
   forall f n, sub_in_env d t n e f -> wf f -> trunc _ n f g -> 
   f |-- (subst_rec d u n) : (subst_rec d U n)) /\
   (forall e T U s, e |-- T >> U : s->
   forall f n, sub_in_env d t n e f -> wf f -> trunc _ n f g -> 
   f |-- (subst_rec d T n) >> (subst_rec d U n) : s).
Proof.
intros g d t H.
apply double_typ_coerce_mut with
 (P := fun e u (U : term) => fun H0 : e |-- u : U =>
 forall f n,
 sub_in_env d t n e f ->
 wf f -> trunc term n f g -> f |-- subst_rec d u n : subst_rec d U n)
 (P0 :=
 fun e T (U : term) s => fun H0 : e |-- T >> U : s =>
 forall f n,
 sub_in_env d t n e f ->
 wf f -> trunc term n f g -> f |-- subst_rec d T n >> subst_rec d U n : s) ;
 simpl in |- *;
 try simpl in IHIH ; 
 try simpl in IHIH0 ; 
 try simpl in IHIH1 ;
 try simpl in IHIH2 ;
 try simpl in IHIH3 ; 
 try simpl in IHIH4 ;
 try simpl in IHIH5 ;
 try simpl in IHIH6 ;
 intros; auto with coc core arith datatypes.

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

apply type_pair with s1 s2 s3 ; auto with coc core arith datatypes.
apply H2 ; auto with coc.
apply wf_var with s1 ; auto with coc.
rewrite <- distr_subst ; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_sum with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with (subst_rec d V (S n)) ; auto with coc.

rewrite distr_subst.
simpl.
apply type_pi2 with (subst_rec d U n) ; auto with coc.
(*
cut (wf (subst_rec d U n :: f)).
intro ; rewrite distr_subst.
apply type_let_in with (subst_rec d U n) s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.
*)
apply type_conv with (subst_rec d U n) s; auto with coc core arith datatypes.

apply coerce_prod with s; auto with coc core arith datatypes.

apply H3 ; auto with coc core.
apply wf_var with s ; auto with coc core.
apply H4 ; auto with coc core.
apply wf_var with s ; auto with coc core.
apply H5 ; auto with coc core.
apply wf_var with s ; auto with coc core.

apply coerce_sum with s s' ; auto with coc core.
apply H3 ; auto with coc core ; apply wf_var with s ; auto with coc core.
apply H4 ; auto with coc core ; apply wf_var with s ; auto with coc core.
apply H5 ; auto with coc core ; apply wf_var with s ; auto with coc core.

apply coerce_sub_l ; auto with coc core.
apply H1 ; auto with coc core ; apply wf_var with set ; auto with coc core.
eapply coerce_sort_l ; auto with coc core.

apply coerce_sub_r ; auto with coc core.
apply H1 ; auto with coc core ; apply wf_var with set ; auto with coc core.
eapply coerce_sort_r ; auto with coc core.

apply coerce_conv with (subst_rec d B n) (subst_rec d C n); auto with coc core.
Qed.

Theorem substitution : forall e t u U, (t :: e) |-- u : U ->
  forall d, e |-- d : t -> e |-- (subst d u) : (subst d U).
Proof.
intros.
unfold subst in |- *.
destruct (double_sub_weak H0). 
apply H1 with (t :: e); auto with coc core arith datatypes.
apply typ_wf with d t; auto with coc core arith datatypes.
Qed.

Theorem substitution_coerce : forall e t T (U : term) s,
  (t :: e) |-- T >> U : s ->
  forall d, e |-- d : t -> e |-- (subst d T) >> (subst d U) : s.
Proof.
intros.
unfold subst in |- *.
destruct (double_sub_weak H0). 
apply H2 with (t :: e); auto with coc core arith datatypes.
apply typ_wf with d t; auto with coc core arith datatypes.
Qed.

Hint Resolve substitution substitution_coerce : coc.

Theorem substitution_coerce_conv_l : forall e t T s,
  (t :: e) |-- T : Srt s ->
  forall d u, e |-- d : t -> e |-- u : t -> conv d u -> 
  e |-- (subst d T) >> (subst u T) : s.
Proof.
intros.
assert(conv T T) ; auto with coc.
pose (conv_conv_subst _ _ _ _ 0 H2 H3) ; auto.
apply conv_coerce ; auto with coc ; try (
change (Srt s) with (subst d (Srt s)) ;
apply substitution with t ; auto with coc core) ; try (
change (Srt s) with (subst u (Srt s)) ;
apply substitution with t ; auto with coc core).
Qed.

Theorem substitution_coerce_conv_l_n : forall e t T s,
  (t :: e) |-- T : Srt s ->
  forall d u, e |-- d : t -> e |-- u : t -> conv d u -> 
  forall n, e |-- (subst d T) >> (subst u T) : s.
Proof.
intros.
assert(conv T T) ; auto with coc.
pose (conv_conv_subst _ _ _ _ 0 H2 H3) ; auto.
apply conv_coerce ; auto with coc ; try (
change (Srt s) with (subst d (Srt s)) ;
apply substitution with t ; auto with coc core) ; try (
change (Srt s) with (subst u (Srt s)) ;
apply substitution with t ; auto with coc core).
Qed.

