Require Import Termes.
Require Import Reduction.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Lemma coerce_weak_weak :
  forall A e T U,
  e |- T >> U ->
  forall n f,
  ins_in_env A n e f -> wf f -> coerce f (lift_rec 1 T n) (lift_rec 1 U n).
intros A e t T IHc.
induction IHc using coerce_mut with 
 (P := fun e t T => fun IHt : typ e t T =>
   forall n f,
   ins_in_env A n e f -> wf f -> typ f (lift_rec 1 t n) (lift_rec 1 T n))
 (P0 := fun e T U => fun IHt : coerce e T U =>
   forall n f,
   ins_in_env A n e f -> wf f -> coerce f (lift_rec 1 T n) (lift_rec 1 U n)) ;
simpl in |- *; try simpl in IHIHc ; try simpl in IHIHc0 ; try simpl in IHIHc1 ; try simpl in IHIHc2 ; try simpl in IHIHc3 ; 
try simpl in IHIHc4 ; intros; auto with coc core arith datatypes.

apply coerce_prod with s ; auto with coc.
apply IHIHt4; auto with coc.
apply wf_var with s.
apply IHIHt1 ; auto with coc core.

apply coerce_sum with s ; auto with coc.
apply IHIHt4; auto with coc.
apply wf_var with s.
apply IHIHt2 ; auto with coc core.

apply coerce_trans with (lift_rec 1 B n) s ; auto with coc core.


  Lemma typ_weak_weak :
   forall A e t T,
   typ e t T ->
   forall n f,
   ins_in_env A n e f -> wf f -> typ f (lift_rec 1 t n) (lift_rec 1 T n).
intros A e t T IHt.
induction IHt ;
simpl in |- *; try simpl in IHIHt ; try simpl in IHIHt1 ; try simpl in IHIHt2 ; try simpl in IHIHt3 ; 
try simpl in IHIHt4 ; intros; auto with coc core arith datatypes.
 (*using typ_mut with 
 (P := fun e t T => fun IHt : typ e t T =>
   forall n f,
   ins_in_env A n e f -> wf f -> typ f (lift_rec 1 t n) (lift_rec 1 T n))
 (P0 := fun e T U => fun IHt : coerce e T U =>
   forall n f,
   ins_in_env A n e f -> wf f -> coerce f (lift_rec 1 T n) (lift_rec 1 U n)) *)

elim (le_gt_dec n0 n); intros; apply type_var;
 auto with coc core arith datatypes.
elim H0; intros.
exists x.
rewrite H3.
unfold lift in |- *.
rewrite simpl_lift_rec; simpl in |- *; auto with coc core arith datatypes.

apply ins_item_ge with A n0 e; auto with coc core arith datatypes.

apply ins_item_lt with A e; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T n :: f)).
intro.
apply type_abs with s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

rewrite distr_lift_subst.
apply type_app with (lift_rec 1 V n); auto with coc core arith datatypes.

apply type_pair with s1 s2 ; auto with coc core arith datatypes.
apply IHIHt3 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

rewrite <- distr_lift_subst.
apply IHIHt4 ; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T n :: f)).
intro.
apply type_prod with s1; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T n :: f)).
intro.
apply type_sum with s1; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T n :: f)).
intro.
apply type_subset ; auto with coc core arith datatypes.
apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with (lift_rec 1 V (S n)) ; auto with coc.

rewrite distr_lift_subst.
simpl.
apply type_pi2 with (lift_rec 1 U n); auto with coc.

cut (wf (lift_rec 1 U n :: f)).
intro.
rewrite distr_lift_subst.
apply type_let_in with (lift_rec 1 U n) s1 s2 ; auto with coc core.
apply wf_var with s1 ; auto with coc core.

apply type_conv with (lift_rec 1 U n) s; auto with coc core arith datatypes.

Qed.

  Lemma coerce_weak_weak :
   forall A e T U,
   e |- T >> U ->
   forall n f,
   ins_in_env A n e f -> wf f -> coerce f (lift_rec 1 T n) (lift_rec 1 U n).
intros A e t T IHc.
induction IHc using coerce_mut with 
 (P := fun e t T => fun IHt : typ e t T =>
   forall n f,
   ins_in_env A n e f -> wf f -> typ f (lift_rec 1 t n) (lift_rec 1 T n))
 (P0 := fun e T U => fun IHt : coerce e T U =>
   forall n f,
   ins_in_env A n e f -> wf f -> coerce f (lift_rec 1 T n) (lift_rec 1 U n)) ;
simpl in |- *; try simpl in IHIHc ; try simpl in IHIHc0 ; try simpl in IHIHc1 ; try simpl in IHIHc2 ; try simpl in IHIHc3 ; 
try simpl in IHIHc4 ; intros; auto with coc core arith datatypes.

elim (le_gt_dec n0 n); intros; apply type_var;
 auto with coc core arith datatypes.
elim i; intros.
exists x.
rewrite H1.
unfold lift in |- *.
rewrite simpl_lift_rec; simpl in |- *; auto with coc core arith datatypes.

apply ins_item_ge with A n0 e; auto with coc core arith datatypes.

apply ins_item_lt with A e; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T n :: f)).
intro.
apply type_abs with s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

rewrite distr_lift_subst.
apply type_app with (lift_rec 1 V n); auto with coc core arith datatypes.

apply type_pair with s1 s2 ; auto with coc core arith datatypes.
apply IHIHc1 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

rewrite <- distr_lift_subst.
apply IHIHc2 ; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T n :: f)).
intro.
apply type_prod with s1; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T n :: f)).
intro.
apply type_sum with s1; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T n :: f)).
intro.
apply type_subset ; auto with coc core arith datatypes.
apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with (lift_rec 1 V (S n)) ; auto with coc.

rewrite distr_lift_subst.
simpl.
apply type_pi2 with (lift_rec 1 U n); auto with coc.

cut (wf (lift_rec 1 U n :: f)).
intro.
rewrite distr_lift_subst.
apply type_let_in with (lift_rec 1 U n) s1 s2 ; auto with coc core.
apply wf_var with s1 ; auto with coc core.

apply type_conv with (lift_rec 1 U n) s; auto with coc core arith datatypes.

apply coerce_prod with s ; auto with coc.
apply IHIHc4; auto with coc.
apply wf_var with s.
apply IHIHc1 ; auto with coc core.

apply coerce_sum with s ; auto with coc.
apply IHIHc4; auto with coc.
apply wf_var with s.
apply IHIHc2 ; auto with coc core.

apply coerce_trans with (lift_rec 1 B n) s ; auto with coc core.
Qed.


  Theorem thinning :
   forall e t T,
   typ e t T -> forall A, wf (A :: e) -> typ (A :: e) (lift 1 t) (lift 1 T).
unfold lift in |- *.
intros.
inversion_clear H0.
apply typ_weak_weak with A e; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.
Qed.

Theorem thinning_coerce : 
   forall e T U,
   e |- T >> U -> 
   forall A, wf (A :: e) -> (A :: e) |- (lift 1 T) >> (lift 1 U).
unfold lift ; intros.
inversion_clear H0.
apply coerce_weak_weak with A e; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.
Qed.

  Lemma thinning_n :
   forall n e f,
   trunc _ n e f ->
   forall t T, typ f t T -> wf e -> typ e (lift n t) (lift n T).
simple induction n.
intros.
rewrite lift0.
rewrite lift0.
replace e with f; auto with coc core arith datatypes.
inversion_clear H; auto with coc core arith datatypes.

do 8 intro.
inversion_clear H0.
intro.
rewrite simpl_lift; auto with coc core arith datatypes.
pattern (lift (S n0) T) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
inversion_clear H0.
change (typ (x :: e0) (lift 1 (lift n0 t)) (lift 1 (lift n0 T))) in |- *.
apply thinning; auto with coc core arith datatypes.
apply H with f; auto with coc core arith datatypes.
apply typ_wf with x (Srt s); auto with coc core arith datatypes.

apply wf_var with s; auto with coc core arith datatypes.
Qed.

  Lemma thinning_n_coerce :
   forall n e f,
   trunc _ n e f ->
   forall T U, f |- T >> U -> wf e -> e |- (lift n T) >> (lift n U).
simple induction n.
intros.
rewrite lift0.
rewrite lift0.
replace e with f; auto with coc core arith datatypes.
inversion_clear H; auto with coc core arith datatypes.

do 8 intro.
inversion_clear H0.
intro.
rewrite simpl_lift; auto with coc core arith datatypes.
pattern (lift (S n0) T) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
inversion_clear H0.
replace (lift (S n0) U) with (lift 1 (lift n0 U)).
apply thinning_coerce; auto with coc core arith datatypes.
apply H with f; auto with coc core arith datatypes.
apply typ_wf with x (Srt s); auto with coc core arith datatypes.

apply wf_var with s; auto with coc core arith datatypes.
rewrite <- simpl_lift.
auto.
Qed.

Lemma wf_sort_lift :
 forall n e t, wf e -> item_lift t e n -> exists s : sort, typ e t (Srt s).
simple induction n.
simple destruct e; intros.
elim H0; intros.
inversion_clear H2.

elim H0; intros.
rewrite H1.
inversion_clear H2.
inversion_clear H.
exists s.
replace (Srt s) with (lift 1 (Srt s)); auto with coc core arith datatypes.
apply thinning; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.

intros.
elim H1; intros.
rewrite H2.
generalize H0.
inversion_clear H3; intros.
rewrite simpl_lift; auto with coc core arith datatypes.
cut (wf l); intros.
elim H with l (lift (S n0) x); intros; auto with coc core arith datatypes.
inversion_clear H3.
exists x0.
change (typ (y :: l) (lift 1 (lift (S n0) x)) (lift 1 (Srt x0))) in |- *.
apply thinning; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.

inversion_clear H3.
apply typ_wf with y (Srt s); auto with coc core arith datatypes.
Qed.

Hint Resolve thinning_n thinning_n_coerce : coc.
