Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Coercion.
Require Import CCPD.Substitution.
Require Import CCPD.Inversion.
Require Import CCPD.Generation.
Require Import CCPD.UnicityOfSorting.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Lemma inv_sub_prod_l_aux : forall e T T' s, e |- T >> T' : s ->
  forall U U' V V', T = Prod U V -> T' = Prod U' V' -> 
  (exists s1, e |- U' >> U : s1) /\ U' :: e |- V >> V' : s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc ; try discriminate.
  
  rewrite H0 in H.
  rewrite H1 in H0.
  inversion H0.
  destruct (generation_prod2 H).
  destruct H2.
  split.
  exists x ; auto with coc.
  apply coerce_refl ; auto with coc.

  inversion H5.
  inversion H6.
  rewrite <- H8.
  rewrite <- H9.
  rewrite <- H10.
  rewrite <- H11.
  split.
  exists s ; auto.
  auto.

  rewrite H6 in H.
  rewrite H7 in H2.
  rewrite H6 in H3.
  rewrite H7 in H5.

  clear IHcoerce.
  induction H4.
  pose (trans_conv_conv _ _ _ H3 H5).
  destruct (inv_conv_prod_sort_l H H2 c).
  split.
  exists x ; auto with coc.
  pose (inv_conv_prod_l _ _ _ _ c).
  intuition.
  apply coerce_conv with U U ; auto with coc.

  destruct (inv_conv_prod_sort_r H H2 c).
  apply coerce_conv with V V ; auto with coc.
  apply (inv_conv_prod_r _ _ _ _ c).

 
  clear IHcoerce1 IHcoerce2.
  pose (inv_conv_prod_l _ _ _ _ H3).
  pose (inv_conv_prod_l _ _ _ _ H5).
  destruct (inv_conv_prod_sort_l H H0 H3).
  destruct (inv_conv_prod_sort_l H1 H2 H5).
  destruct a ; destruct a0.
  pose (unique_sort H13 H4).
  pose (unique_sort H12 H8).

  split.
  exists s.
  apply coerce_conv with A' A0 ; auto with coc.
  rewrite <- e0 ; auto.
  rewrite <- e1 ; auto.
  
  pose (inv_conv_prod_r _ _ _ _ H3).
  pose (inv_conv_prod_r _ _ _ _ H5).
  destruct (inv_conv_prod_sort_r H H0 H3).
  destruct (inv_conv_prod_sort_r H1 H2 H5).

  rewrite e0 in H13.
  rewrite e0 in H14.
  rewrite e1 in H11.
  rewrite e1 in H12.
  
  apply coerce_conv with B B' ; auto with coc.

  apply typ_conv_env with (A0 :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  apply coerce_conv with A' A0 ; auto with coc.
  apply wf_var with s ; auto with coc.

  apply typ_conv_env with (A0 :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  apply coerce_conv with A' A0 ; auto with coc.
  apply wf_var with s ; auto with coc.

  apply coerce_conv_env with (A' :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  apply coerce_conv with A' A' ; auto with coc.
  apply wf_var with s ; auto with coc.

  elim conv_prod_sum with U V A0 B ; auto with coc.

  elim conv_prod_subset with U V U0 P ; auto with coc.

  elim conv_prod_subset with U' V' U'0 P ; auto with coc.

  apply IHcoerce ; auto with coc.
  apply trans_conv_conv with A0 ; auto with coc.
  apply trans_conv_conv with D0 ; auto with coc.
Qed.

Lemma inv_sub_prod_l : forall e U U' V V' s, e |- Prod U V >> Prod U' V' : s ->
  exists s1, e |- U' >> U : s1.
Proof.
  intros.
  destruct (inv_sub_prod_l_aux H (refl_equal (Prod U V)) (refl_equal (Prod U' V'))).
  assumption.
Qed.

Lemma inv_sub_prod_r : 
  forall e U U' V V' s, e |- Prod U V >> Prod U' V' : s ->
  U' :: e |- V >> V' : s.
Proof.
  intros.
  destruct (inv_sub_prod_l_aux H (refl_equal (Prod U V)) (refl_equal (Prod U' V'))).
  assumption.
Qed.

Lemma inv_sub_sum_aux : forall e T T' s, e |- T >> T' : s ->
  forall U U' V V', T = Sum U V -> T' = Sum U' V' -> 
  (exists s1, e |- U >> U' : s1) /\ U :: e |- V >> V' : s.
Proof.

  induction 1 ; simpl ; intros ; auto with coc ; try discriminate.
  
  rewrite H0 in H.
  rewrite H1 in H0.
  inversion H0.
  destruct (generation_sum2 H).
  destruct H2.
  split.
  exists x ; auto with coc.
  intuition ; apply coerce_refl ; auto with coc.

  inversion H7.
  inversion H8.
  rewrite <- H10.
  rewrite <- H11.
  rewrite <- H12.
  rewrite <- H13.
  split.
  exists s ; auto.
  auto.

  rewrite H6 in H.
  rewrite H7 in H2.
  rewrite H6 in H3.
  rewrite H7 in H5.

  clear IHcoerce.
  induction H4.
  pose (trans_conv_conv _ _ _ H3 H5).
  destruct (inv_conv_sum_sort_l H H2 c).
  split.
  exists x ; auto with coc.
  pose (inv_conv_sum_l _ _ _ _ c).
  intuition.
  apply coerce_conv with U U ; auto with coc.

  destruct (inv_conv_sum_sort_r H H2 c).
  apply coerce_conv with V V ; auto with coc.
  apply (inv_conv_sum_r _ _ _ _ c).

  elim conv_prod_sum with A' B' U' V' ; auto with coc.

  clear IHcoerce1 IHcoerce2.
  pose (inv_conv_sum_l _ _ _ _ H3).
  pose (inv_conv_sum_l _ _ _ _ H5).
  destruct (inv_conv_sum_sort_l H H0 H3).
  destruct (inv_conv_sum_sort_l H1 H2 H5).
  destruct a ; destruct a0.
  pose (unique_sort H14 H8).
  pose (unique_sort H15 H4).

  split.
  exists s.
  apply coerce_conv with A0 A' ; auto with coc.
  rewrite <- e0 ; auto.
  rewrite <- e1 ; auto.
  
  pose (inv_conv_sum_r _ _ _ _ H3).
  pose (inv_conv_sum_r _ _ _ _ H5).
  destruct (inv_conv_sum_sort_r H H0 H3).
  destruct (inv_conv_sum_sort_r H1 H2 H5).

  rewrite e0 in H13.
  rewrite e0 in H14.
  rewrite e1 in H15.
  rewrite e1 in H16.
  
  apply coerce_conv with B B' ; auto with coc.

  apply typ_conv_env with (A' :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  apply coerce_conv with A0 A' ; auto with coc.
  apply wf_var with s ; auto with coc.

  apply typ_conv_env with (A' :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  apply coerce_conv with A0 A' ; auto with coc.
  apply wf_var with s ; auto with coc.

  apply coerce_conv_env with (A0 :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  apply coerce_conv with A0 A0 ; auto with coc.
  apply wf_var with s ; auto with coc.

  elim conv_subset_sum with U0 P U V ; auto with coc.

  elim conv_subset_sum with U'0 P U' V' ; auto with coc.

  apply IHcoerce ; auto with coc.
  apply trans_conv_conv with A0 ; auto with coc.
  apply trans_conv_conv with D0 ; auto with coc.
Qed.

Lemma inv_sub_sum_l : forall e U U' V V' s, e |- Sum U V >> Sum U' V' : s ->
  exists s1, e |- U >> U' : s1.
Proof.
  intros.
  destruct (inv_sub_sum_aux H (refl_equal (Sum U V)) (refl_equal (Sum U' V'))).
  assumption.
Qed.

Lemma inv_sub_sum_r : forall e U U' V V' s, e |- Sum U V >> Sum U' V' : s ->
  U :: e |- V >> V' : s.
Proof.
  intros.
  destruct (inv_sub_sum_aux H (refl_equal (Sum U V)) (refl_equal (Sum U' V'))).
  assumption.
Qed.



Lemma inv_sub_prod_l_aux : forall e T T' s, e |- T >> T' : s ->
  forall U U' V V', T = Prod U V -> T' = Prod U' V' -> 
  exists s1, e |- U' >> U : s1.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  rewrite H2 in H1.
  rewrite H3 in H1.
  pose (inv_conv_prod_l _ _ _ _ H1).
  rewrite H2 in H.
  rewrite H3 in H0.
  apply inv_typ_prod with e U V (Srt s) ; auto with coc ; intros.
  apply inv_typ_prod with e U' V' (Srt s) ; auto with coc ; intros.
  exists s1.
  apply coerce_conv ; auto with coc.
  Focus 6.

  rewrite H1 in H.
  inversion H.
  rewrite H2 in H0.
  inversion H0.
  
  Focus 2.
  rewrite <- H17 in H5.
  pose (inv_conv_prod_l _ _ _ _ H5).
  exists s1.
  apply coerce_trans with A1 ; auto with coc.
  apply coerce_conv ; auto with coc.


Admitted.

Lemma inv_sub_prod_l : forall e U U' V V' s, e |- Prod U V >> Prod U' V' : s ->
  exists s1, e |- U' >> U : s1.
Proof.
  intros.
  eapply (inv_sub_prod_l_aux e (Prod U V) (Prod U' V') s H)  ; auto.
Qed.

Lemma inv_sub_prod_r_aux : forall e T T' s, e |- T >> T' : s ->
  forall U U' V V', T = Prod U V -> T' = Prod U' V' -> 
  U' :: e |- V >> V' : s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc ; try discriminate.
  rewrite H2 in H1.
  rewrite H3 in H1.
  pose (inv_conv_prod_r _ _ _ _ H1).
  rewrite H2 in H.
  rewrite H3 in H0.
  apply inv_typ_prod2 with e U V (Srt s) ; auto with coc ; intros.
  apply inv_typ_prod2 with e U' V' (Srt s) ; auto with coc ; intros.
  
  apply coerce_conv ; auto with coc.
  cut (e |- U' >> U : s0) ; intros.

  assert(coerce_in_env (U :: e) (U' :: e)).
  apply coerce_env_hd with s0 ; auto.
  
  assert (wf (U' :: e)) ; try apply wf_var with s0 ; auto.
  apply (typ_conv_env _ _ _ H5 (U' :: e) H9 H10).
  
  Focus 2.
  inversion H5.
  inversion H6.
  rewrite <- H10.
  rewrite <- H9.
  rewrite <- H11.
  assumption.

  Focus 2.
  rewrite H1 in H.
  rewrite H2 in H0.
Admitted.

Lemma inv_sub_prod_r : forall e U U' V V' s, e |- Prod U V >> Prod U' V' : s ->
  U' :: e |- V >> V' : s.
Proof.
  intros.
  eapply (inv_sub_prod_r_aux e (Prod U V) (Prod U' V') s H)  ; auto.
Qed.

Lemma inv_sub_sum_l : forall e U U' V V' s, e |- Sum U V >> Sum U' V' : s ->
  exists s1, e |- U >> U' : s1.
Proof.
  intros.
Admitted.

Lemma inv_sub_sum_r : forall e U U' V V' s, e |- Sum U V >> Sum U' V' : s ->
  U :: e |- V >> V' : s.
Proof.
  intros.
Admitted.

Lemma inv_sub_sum_r2 : forall e U U' V V' s, e |- Sum U V >> Sum U' V' : s ->
  U' :: e |- V >> V' : s.
Proof.
  intros.
Admitted.

Lemma typ_red_env : forall e U V s1, e |- U : Srt s1 -> e |- V : Srt s1 ->
  red1 U V -> forall W T, U :: e |- W : T -> V :: e |- W : T.
Proof.
  intros.
  assert(coerce_in_env (U :: e) (V :: e)).
  apply coerce_env_hd with s1.
  apply coerce_conv ; auto.
  apply one_step_conv_exp ; auto.
  pose (typ_conv_env). 
  assert(wf (V :: e)).
  apply wf_var with s1 ; auto with coc.
  apply (typ_conv_env _ _ _ H2 (V :: e) H3 H4).
Qed.

Lemma subj_red : forall e t T, typ e t T -> forall u, red1 t u -> typ e u T.
induction 1 using typ_dep ; intros.
inversion_clear H.

inversion_clear H.

inversion_clear H.

inversion_clear H2.

pose (IHtyp1 _ H3).
cut (wf (M' :: e)); intros.
assert(coerce_in_env (T :: e) (M' :: e)).
apply coerce_env_hd with s1.
apply coerce_conv ; auto.
apply one_step_conv_exp ; auto.

pose (typ_conv_env _ _ _ H0 (M' :: e) H4 H2).
pose (typ_conv_env _ _ _ H1 (M' :: e) H4 H2).
assert (e |- Prod T U : Srt s2).
apply type_prod with s1 ; auto with coc.
assert (e |- Prod M' U : Srt s2).
apply type_prod with s1 ; auto with coc.
apply type_conv with (Prod M' U) s2; auto with coc core arith datatypes.
apply type_abs with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

pose (IHtyp3 _ H3).
apply type_abs with s1 s2; auto with coc core arith datatypes.

elim type_sorted with e u (Prod V Ur); intros;
 auto with coc core arith datatypes.
inversion_clear H2.
destruct H2.
apply inv_typ_prod2 with e V Ur (Srt x); intros;
 auto with coc core arith datatypes.
generalize H H0. clear H H0.
inversion_clear H1; intros.
apply inv_typ_abs with e T M (Prod V Ur); intros;
 auto with coc core arith datatypes.
pose (coerce_sort_r _ _ _ _ H8).
pose (unique_sort H2 t).
rewrite <- e0 in H1.
rewrite <- e0 in H7.
rewrite <- e0 in H8.
destruct (inv_sub_prod_l _ _ _ _ _ _ H9); auto with coc core arith datatypes.
apply type_conv with (subst v T0) x; auto with coc core arith datatypes.
apply substitution with T; auto with coc core arith datatypes.
pose (coerce_sort_r _ _ _ _ H10).
pose (coerce_sort_l _ _ _ _ H10).
pose (unique_sort H5 t0).
pose (unique_sort H3 t1).
rewrite e2 in H3.
rewrite e1 in H5.
apply type_conv with V x0; auto with coc core arith datatypes.

replace (Srt x) with (subst v (Srt x)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

replace (Srt x) with (subst v (Srt x)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

assert(coerce_in_env (T :: e) (V :: e)).
apply coerce_env_hd with x0 ; auto.
cut (wf (V :: e)) ; intros.
apply (typ_conv_env _ _ _ H7 (V :: e) H11 H12).
apply wf_var with s1 ; auto.

clear H10.
pose (inv_sub_prod_r _ _ _ _ _ _ H9).
apply (substitution_coerce e V _ _ _ c v H).

apply type_app with V; auto with coc core arith datatypes.

cut(e |- subst N2 Ur : Srt x).
cut(e |- subst v Ur : Srt x).
intros.
apply type_conv with (subst N2 Ur) x; auto with coc core arith datatypes.
apply type_app with V; auto with coc core arith datatypes.

apply coerce_conv ; auto.
unfold subst in |- *.
apply conv_conv_subst; auto with coc core arith datatypes.

replace (Srt x) with (subst v (Srt x)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

pose (IHtyp1 _ H).
replace (Srt x) with (subst N2 (Srt x)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

assert(e |- Sum U V : Srt s2).
apply type_sum with s1 ; auto with coc core.

inversion_clear H3.
inversion_clear H5.
destruct s.
destruct H5.
rewrite H5 in H3.
inversion H3.

pose (IHtyp1 _ H3).
assert(e |- Sum N1 V : Srt s2).
apply type_sum with s1 ; auto with coc core.

apply typ_red_env with U s1 ; auto with coc core.
right ; auto.

apply type_conv with (Sum N1 V) s2 ; auto with coc.
apply type_pair with s1 s2 ; auto with coc core.
apply type_conv with U s1 ; auto with coc core.
apply typ_red_env with U s1; auto with coc core arith datatypes.
right ; auto.

destruct s.
destruct H5.
rewrite H6 in H3.
inversion H3.

pose (IHtyp3 _ H3).
assert(e |- Sum U N2 : Srt s2).
apply type_sum with s1 ; auto with coc core.
right ; auto.

apply type_conv with (Sum U N2) s2 ; auto with coc.
apply type_pair with s1 s2 ; auto with coc core.
apply type_conv with (subst u V) s2 ; auto with coc core.
replace (Srt s2) with (subst u (Srt s2)).
apply substitution with U ; auto with coc core arith datatypes.
simpl ; auto.
replace (Srt s2) with (subst u (Srt s2)).
apply substitution with U ; auto with coc core arith datatypes.
simpl ; auto.
apply substitution_coerce with U ; auto with coc core arith datatypes.
right ; auto.

pose (IHtyp2 _ H5).
apply type_pair with s1 s2 ; auto with coc core.

apply type_conv with (subst u V) s2 ; auto with coc.
replace (Srt s2) with (subst N1 (Srt s2)).
apply substitution with U ; auto with coc core arith datatypes.
simpl ; auto.
replace (Srt s2) with (subst u (Srt s2)).
apply substitution with U ; auto with coc core arith datatypes.
simpl ; auto.
apply substitution_coerce2 with U ; auto with coc core arith datatypes.

pose (IHtyp4 _ H5).
apply type_pair with s1 s2 ; auto with coc core.

inversion_clear H1.
apply type_prod with s1; auto with coc core arith datatypes.
apply typ_red_env with T s1; auto with coc core arith datatypes.

apply type_prod with s1; auto with coc core arith datatypes.

inversion_clear H1.
apply type_sum with s1 ; auto with coc core.
apply typ_red_env with T s1 ; auto with coc core.
destruct s.
destruct H1.
rewrite H1 in H2.
inversion H2.
right ; auto.

apply type_sum with s1 ; auto with coc core.
destruct s.
destruct H1.
rewrite H3 in H2.
inversion H2.
right ; auto.

inversion H1.
apply type_subset ; auto with coc core.
apply typ_red_env with T set ; auto with coc core.

apply type_subset ; auto with coc core.

generalize H IHtyp ; clear H IHtyp.
inversion_clear H0 ; intros.
induction (type_sorted H).
discriminate.
induction H0.
apply inv_typ_sum2 with e U V (Srt x) ; auto ; intros.
apply inv_typ_pair with e T u N (Sum U V) ; auto with coc ; intros.

destruct (inv_sub_sum_l _ _ _ _ _ _ H9).
pose (unicity_coerce_r H10 H4).
pose (coerce_sort_l _ _ _ _ c).

apply type_conv with U0 s0 ; auto with coc.
apply coerce_sym ; auto.

pose (IHtyp _ H).
apply type_pi1 with V ; auto.

generalize H IHtyp ; clear H IHtyp.
inversion_clear H0 ; intros.

apply inv_typ_pair with e T M u (Sum U V) ; auto with coc ; intros.
apply inv_typ_sum2 with e U V (Srt s) ; auto with coc ; intros.

apply type_conv with (subst M V0) s; auto with coc core.
replace (Srt s) with (subst (Pi1 (Pair T M u)) (Srt s)).
apply substitution with U ; auto with coc core arith datatypes.
apply type_pi1 with V  ; auto with coc core arith datatypes.
simpl ; auto.
replace (Srt s) with (subst M (Srt s)).
apply substitution with U0 ; auto with coc core arith datatypes.
simpl ; auto.

pose (coerce_sym _ _ _ _ (inv_sub_sum_r2 _ _ _ _ _ _ H6)).
apply coerce_trans with (subst M V).
apply substitution_coerce with U0 ; auto with coc.

apply substitution_coerce2 with U0 ; auto with coc.
apply (coerce_sort_r _ _ _ _ c).
apply type_pi1 with V0.
apply type_conv with (Sum U V) s ; auto with coc.
apply (coerce_sort_r _ _ _ _ H6).

pose (IHtyp _ H).
destruct (type_sorted t0) ; try discriminate.
destruct H1.
apply inv_typ_sum2 with e U V (Srt x) ; auto with coc ; intros.
apply type_conv with (subst (Pi1 N) V) x ; auto with coc.
apply type_pi2 with U ; auto with coc.
replace (Srt x) with (subst (Pi1 t) (Srt x)).
apply substitution with U ; auto with coc core arith datatypes.
apply type_pi1 with V ; auto with coc.
simpl ; auto.
replace (Srt x) with (subst (Pi1 N) (Srt x)).
apply substitution with U ; auto with coc core arith datatypes.
apply type_pi1 with V ; auto with coc.
simpl ; auto.
apply substitution_coerce2 with U ; auto with coc.
apply type_pi1 with V ; auto with coc.
apply type_pi1 with V ; auto with coc.

apply type_conv with U s; auto with coc core arith datatypes.
Qed.

  Theorem subject_reduction :
   forall e t u, red t u -> forall T, typ e t T -> typ e u T.
simple induction 1; intros; auto with coc core arith datatypes.
apply subj_red with P; intros; auto with coc core arith datatypes.
Qed.