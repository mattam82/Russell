Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.TypesNoDerivs.
Require Import Lambda.TPOSR.LeftReflexivity.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Lemma ind_thinning : forall A,
  (forall e u v T, e |-- u -> v : T ->
   forall n f, ins_in_lenv A n e f -> tposr_wf f ->
   f |-- (llift_rec 1 u n) -> (llift_rec 1 v n) : (llift_rec 1 T n)) /\
  (forall e, tposr_wf e -> True) /\
  (forall e u v s, e |-- u ~= v : s ->
   forall n f, ins_in_lenv A n e f -> tposr_wf f ->
   f |-- (llift_rec 1 u n) ~= (llift_rec 1 v n) : s) /\
  (forall e u v s, e |-- u >-> v : s ->
   forall n f, ins_in_lenv A n e f -> tposr_wf f ->
   f |-- (llift_rec 1 u n) >-> (llift_rec 1 v n) : s).
Proof.
intros A.
apply ind_tposr_wf_eq_coerce with 
 (P := fun e u v T => fun IH : e |-- u -> v : T =>
   forall n f,
   ins_in_lenv A n e f -> tposr_wf f ->
   f |-- (llift_rec 1 u n) -> (llift_rec 1 v n) : (llift_rec 1 T n))
  (P0 := fun e => fun H : tposr_wf e => 
   True)
  (P1 := fun e u v s => fun H : e |-- u ~= v : s =>
   forall n f, ins_in_lenv A n e f -> tposr_wf f ->
   f |-- (llift_rec 1 u n) ~= (llift_rec 1 v n) : s)
  (P2 := fun e u v s => fun H : e |-- u >-> v : s =>
   forall n f, ins_in_lenv A n e f -> tposr_wf f ->
   f |-- (llift_rec 1 u n) >-> (llift_rec 1 v n) : s) ;
   simpl in |- *; 
   try simpl in IHtposr1 ; 
   try simpl in IHtposr0 ; 
   try simpl in IHtposr2 ; 
   try simpl in IHtposr3 ; 
   try simpl in IHtposr4 ; 
   try simpl in IHtposr5 ; 
   intros; auto with coc core arith datatypes.

elim (le_gt_dec n0 n); intros; apply tposr_var;
 auto with coc core arith datatypes.
elim i; intros.
exists x.
rewrite H2.
unfold llift in |- *.
rewrite simpl_llift_rec; simpl in |- *; auto with coc core arith datatypes.

apply ins_item_ge with A n0 e; auto with coc core arith datatypes.

apply ins_item_lt with A e; auto with coc core arith datatypes.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by (apply wf_cons with s1 ; eauto with coc).
apply tposr_prod with s1 ; auto with coc core arith datatypes.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by (apply wf_cons with s1 ; eauto with coc).
apply tposr_abs with s1 (llift_rec 1 B' (S n)) s2 ; auto with coc core arith datatypes.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by (apply wf_cons with s1 ; eauto with coc).
rewrite distr_llift_lsubst ; auto with coc.
apply tposr_app with (llift_rec 1 A0 n) (llift_rec 1 A' n) s1 s2; auto with coc core arith datatypes.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by (apply wf_cons with s1 ; eauto with coc).
rewrite distr_llift_lsubst ; auto with coc.
rewrite distr_llift_lsubst ; auto with coc.

apply tposr_beta with (llift_rec 1 A' n) s1 (llift_rec 1 B' (S n)) s2; auto with coc core arith datatypes.

apply tposr_conv with (llift_rec 1 A0 n) s; auto with coc.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by (apply wf_cons with set ; eauto with coc).
apply tposr_subset ; auto with coc.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by (apply wf_cons with s1 ; eauto with coc).
apply tposr_sum with s1 s2; auto with coc core arith datatypes.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by (apply wf_cons with s1 ; eauto with coc).
apply tposr_pair with s1 s2 s3 ; auto with coc.
rewrite <- distr_llift_lsubst ; auto with coc.

apply tposr_pi1 with s1 s2 s3 ; auto with coc.
apply H1 ; eauto with coc.
apply wf_cons with s1 ; eauto with coc.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by (apply wf_cons with s1 ; eauto with coc).
apply tposr_pi1_red with s1 s2 s3 (llift_rec 1 A'' n) (llift_rec 1 B'' (S n)) (llift_rec 1 v' n) ; auto with coc.

(*apply tposr_pi1_red with (llift_rec 1 A' n) s1 (llift_rec 1 B' (S n))  s2 s3 (llift_rec 1 v' n); auto with coc.
rewrite <- distr_llift_lsubst.
auto with coc.
*)
assert (tposr_wf (llift_rec 1 A0 n :: f)) by (apply wf_cons with s1 ; eauto with coc).
rewrite distr_llift_lsubst.
simpl.
apply tposr_pi2 with s1 s2 s3 ; auto with coc.

assert (tposr_wf (llift_rec 1 A0 n :: f)) by (apply wf_cons with s1 ; eauto with coc).
rewrite distr_llift_lsubst.
simpl.
apply tposr_pi2_red with s1 s2 s3 (llift_rec 1 A'' n) (llift_rec 1 B'' (S n)) (llift_rec 1 u' n) ; auto with coc.
(*
apply tposr_pi2_red with (llift_rec 1 A' n) s1 (llift_rec 1 B' (S n))  s2 s3 (llift_rec 1 u' n); auto with coc.
rewrite <- distr_llift_lsubst.
auto with coc.
*)
apply tposr_eq_trans with (llift_rec 1 X n) ; auto with coc.


apply tposr_coerce_prod with s ; eauto with coc ecoc.


apply tposr_coerce_sum with s s' ; eauto with coc ecoc.

apply tposr_coerce_sub_l ; eauto with coc ecoc.

apply tposr_coerce_sub_r ; eauto with coc ecoc.

apply tposr_coerce_trans with (llift_rec 1 B n) ; auto with coc.
Qed.

Corollary thinning :
   forall e t t' T,
   e |-- t -> t' : T -> forall A, tposr_wf (A :: e) -> (A :: e) |-- llift 1 t -> llift 1 t' : (llift 1 T).
Proof.
unfold llift in |- *.
intros.
apply (proj1 (ind_thinning A)) with e ; auto with coc.
Qed.

Corollary thinning_eq :
   forall e t t' s,
   e |-- t ~= t' : s -> 
   forall A, tposr_wf (A :: e) -> (A :: e) |-- (llift 1 t) ~= llift 1 t' : s.
Proof.
unfold llift in |- *.
intros.
apply (proj1 (proj2 (proj2 (ind_thinning A)))) with e ; auto with coc.
Qed.

Corollary thinning_coerce :
   forall e t t' s,
   e |-- t >-> t' : s -> 
   forall A, tposr_wf (A :: e) -> (A :: e) |-- (llift 1 t) >-> llift 1 t' : s.
Proof.
unfold llift in |- *.
intros.
apply (proj2 (proj2 (proj2 (ind_thinning A)))) with e ; auto with coc.
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
apply wf_tposr with x x (Srt_l s); auto with coc core arith datatypes.

apply wf_cons with s; auto with coc core arith datatypes.
Qed.

Lemma thinning_n_eq :
   forall n e f,
   trunc _ n e f ->
   forall t t' s, f |-- t ~= t' : s -> tposr_wf e -> e |-- (llift n t) ~= (llift n t') : s.
Proof.
simple induction n.
intros.
do 2 rewrite llift0.
replace e with f; auto with coc core arith datatypes.
inversion_clear H; auto with coc core arith datatypes.

do 8 intro.
inversion_clear H0.
intro.
rewrite simpl_llift; auto with coc core arith datatypes.

pattern (llift (S n0) t') in |- *.
rewrite simpl_llift; auto with coc core arith datatypes.
intros.
inversion_clear H2.
apply thinning_eq; auto with coc core arith datatypes.
apply H with f; auto with coc core arith datatypes.
apply wf_tposr with x x (Srt_l s0); auto with coc core arith datatypes.

apply wf_cons with s0; auto with coc core arith datatypes.
Qed.

Lemma thinning_n_coerce :
   forall n e f,
   trunc _ n e f ->
   forall t t' s, f |-- t >-> t' : s -> tposr_wf e -> e |-- (llift n t) >-> (llift n t') : s.
Proof.
simple induction n.
intros.
do 2 rewrite llift0.
replace e with f; auto with coc core arith datatypes.
inversion_clear H; auto with coc core arith datatypes.

do 8 intro.
inversion_clear H0.
intro.
rewrite simpl_llift; auto with coc core arith datatypes.

pattern (llift (S n0) t') in |- *.
rewrite simpl_llift; auto with coc core arith datatypes.
intros.
inversion_clear H2.
apply thinning_coerce; auto with coc core arith datatypes.
apply H with f; auto with coc core arith datatypes.
apply wf_tposr with x x (Srt_l s0); auto with coc core arith datatypes.

apply wf_cons with s0; auto with coc core arith datatypes.
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
exists (llift 1 l).
apply thinning; auto with coc core arith datatypes.
apply wf_cons with s; auto with coc core arith datatypes.

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
apply wf_cons with s; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.

inversion_clear H3.
apply (wf_tposr H5); auto with coc core arith datatypes.
Qed.

Hint Resolve thinning thinning_eq thinning_coerce thinning_n : coc.
