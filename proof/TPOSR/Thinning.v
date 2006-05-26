Require Import TPOSR.Terms.
Require Import TPOSR.Reduction.
Require Import TPOSR.LiftSubst.
Require Import TPOSR.Env.
Require Import TPOSR.Conv.
Require Import TPOSR.Types.
Require Import TPOSR.Basic.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Lemma weak_weak : forall A,
  (forall e u v T, e |-- u -> v : T ->
   forall n f, ins_in_lenv A n e f -> tposr_wf f -> 
   f |-- (llift_rec 1 u n) -> (llift_rec 1 v n) : (llift_rec 1 T n)).
Proof.
intros A.
induction 1 using ind_tposr with 
 (P := fun e u v T => fun IH : e |-- u -> v : T =>
   forall n f,
   ins_in_lenv A n e f -> tposr_wf f -> f |-- (llift_rec 1 u n) -> (llift_rec 1 v n) : (llift_rec 1 T n)) ;
   simpl in |- *; 
   try simpl in IHtposr1 ; 
   try simpl in IHtposr0 ; 
   try simpl in IHtposr2 ; 
   try simpl in IHtposr3 ; 
   try simpl in IHtposr4 ; 
   intros; auto with coc core arith datatypes.

elim (le_gt_dec n0 n); intros; apply tposr_var;
 auto with coc core arith datatypes.
elim i; intros.
exists x.
rewrite H1.
unfold llift in |- *.
rewrite simpl_llift_rec; simpl in |- *; auto with coc core arith datatypes.

apply ins_item_ge with A n0 e; auto with coc core arith datatypes.

apply ins_item_lt with A e; auto with coc core arith datatypes.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by apply wf_cons with (llift_rec 1 A' n) s1 ; auto with coc.
apply tposr_prod with s1 ; auto with coc core arith datatypes.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by apply wf_cons with (llift_rec 1 A' n) s1 ; auto with coc.
apply tposr_abs with s1 (llift_rec 1 B' (S n)) s2 ; auto with coc core arith datatypes.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by apply wf_cons with (llift_rec 1 A' n) s1 ; auto with coc.
rewrite distr_llift_lsubst ; auto with coc.
apply tposr_app with (llift_rec 1 A0 n) (llift_rec 1 A' n) s1 s2; auto with coc core arith datatypes.


assert (tposr_wf (llift_rec 1 A0 n :: f)) by apply wf_cons with (llift_rec 1 A' n) s1 ; auto with coc.
rewrite distr_llift_lsubst ; auto with coc.
rewrite distr_llift_lsubst ; auto with coc.

apply tposr_beta with (llift_rec 1 A' n) s1 (llift_rec 1 B' (S n)) s2; auto with coc core arith datatypes.

apply tposr_red with (llift_rec 1 A0 n) s; auto with coc.

apply tposr_exp with (llift_rec 1 B n) s; auto with coc.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by apply wf_cons with (llift_rec 1 A' n) set ; auto with coc.
apply tposr_subset ; auto with coc.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by apply wf_cons with (llift_rec 1 A' n) s1 ; auto with coc.
apply tposr_sum with s1 s2; auto with coc core arith datatypes.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by apply wf_cons with (llift_rec 1 A' n) s1 ; auto with coc.
apply tposr_pair with s1 s2 s3 ; auto with coc.
rewrite <- distr_llift_lsubst ; auto with coc.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by apply wf_cons with (llift_rec 1 A' n) s1 ; auto with coc.
apply tposr_pi1 with s1 s2 s3 ; auto with coc.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by apply wf_cons with (llift_rec 1 A' n) s1 ; auto with coc.
apply tposr_pi1_red with (llift_rec 1 A' n) s1 (llift_rec 1 B' (S n))  s2 s3 (llift_rec 1 u' n) (llift_rec 1 v' n); auto with coc.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by apply wf_cons with (llift_rec 1 A' n) s1 ; auto with coc.
rewrite distr_llift_lsubst.
simpl.
apply tposr_pi2 with s1 s2 s3 ; auto with coc.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by apply wf_cons with (llift_rec 1 A' n) s1 ; auto with coc.
rewrite distr_llift_lsubst.
simpl.
apply tposr_pi2_red with (llift_rec 1 A' n) s1 (llift_rec 1 B' (S n))  s2 s3 (llift_rec 1 u' n) (llift_rec 1 v' n); auto with coc.
Qed.

  Theorem thinning :
   forall e t t' T,
   e |-- t -> t' : T -> forall A, tposr_wf (A :: e) -> (A :: e) |-- (llift 1 t) -> llift 1 t' : (llift 1 T).
Proof.
unfold llift in |- *.
intros.
inversion_clear H0.
apply weak_weak with A e ; auto with coc.
apply wf_cons with A' s; auto with coc core arith datatypes.
Qed.

Lemma thinning_n :
   forall n e f,
   trunc _ n e f ->
   forall t t' T, f |-- t -> t' : T -> tposr_wf e -> e |-- (llift n t) -> (llift n t') : (llift n T).
Proof.
simple induction n.
intros.
do 3 rewrite llift0.
replace e with f; auto with coc core arith datatypes.
inversion_clear H; auto with coc core arith datatypes.

do 8 intro.
inversion_clear H0.
intro.
rewrite simpl_llift; auto with coc core arith datatypes.

pattern (llift (S n0) t') in |- *.
rewrite simpl_llift; auto with coc core arith datatypes.
pattern (llift (S n0) T) in |- *.
rewrite simpl_llift; auto with coc core arith datatypes.
intros.
inversion_clear H2.
apply thinning; auto with coc core arith datatypes.
apply H with f; auto with coc core arith datatypes.
apply wf_tposr with x A' (Srt_l s); auto with coc core arith datatypes.

apply wf_cons with A' s; auto with coc core arith datatypes.
Qed.

Lemma wf_sort_lift :
 forall n e t, tposr_wf e -> item_llift t e n -> exists s : sort, exists t', e |-- t -> t' : (Srt_l s).
simple induction n.
simple destruct e; intros.
elim H0; intros.
inversion_clear H2.

elim H0; intros.
rewrite H1.
inversion_clear H2.
inversion_clear H.
exists s.
replace (Srt_l s) with (llift 1 (Srt_l s)); auto with coc core arith datatypes.
exists (llift 1 A').
apply thinning; auto with coc core arith datatypes.
apply wf_cons with A' s; auto with coc core arith datatypes.

intros.
elim H1; intros.
rewrite H2.
generalize H0.
inversion_clear H3; intros.
rewrite simpl_llift; auto with coc core arith datatypes.
cut (tposr_wf l); intros.
elim H with l (llift (S n0) x); intros; auto with coc core arith datatypes.
inversion_clear H3.
exists x0.
destruct H6.
exists (llift 1 x1).
change (tposr (y :: l) (llift 1 (llift (S n0) x)) (llift 1 x1) (llift 1 (Srt_l x0))) in |- *.
apply thinning; auto with coc core arith datatypes.
apply wf_cons with A' s; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.

inversion_clear H3.
apply (wf_tposr H5); auto with coc core arith datatypes.
Qed.

Hint Resolve thinning thinning_n : coc.
