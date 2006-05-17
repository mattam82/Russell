Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import Conv_Dec.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Substitution.
Require Import CCPD.Coercion.
Require Import CCPD.GenerationNotKind.
Require Import CCPD.GenerationCoerce.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.


Lemma wf_is_sorted : forall e, wf e ->
  forall x n, item _ x e n -> forall s, x = Srt s -> is_prop s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  elim (inv_nth_nl _ _ _ H).
  pose (item_trunc).
  induction (item_trunc _ _ _ _ H0).

  pose (wf_sort).
  pose (wf_var H).
  induction (wf_sort  H2 w H0).
  rewrite H1 in H3.
  pose (typ_sort H3).
  intuition.
Qed.


Lemma inv_lift_sort : forall t s n, lift n t = Srt s -> t = Srt s.
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
auto.
Qed.

Lemma gen_sorting_var_aux : forall e t T, e |- t : T ->
  forall n, t = Ref n -> 
  forall s, T = (Srt s) ->
  is_prop s.
Proof.
  induction 1 using typ_mutwf with
   (P := fun e t T => fun H : e |- t : T =>
   forall n, t = Ref n -> 
   forall s, T = (Srt s) ->
   is_prop s)
   (P0 := fun e T U s => fun H : e |- T >> U : s =>
   True)
   (P1 := fun e => fun H : wf e =>
   forall s, forall n, item _ (Srt s) e n -> is_prop s)
 ; try (simpl ; intros ; try discriminate ; auto with coc).
 
  rewrite H0 in i.
  destruct i.
  rewrite (inv_lift_sort x (S n) (sym_eq H1)) in H2.
  apply (IHtyp s n).
  auto.
 
  rewrite H3 in H0.
  pose (typ_sort H0).
  intuition.
 
  elim (inv_nth_nl _ _ _ H).

  pose (wf_is_sorted).
  apply wf_is_sorted with (T :: e) (Srt s0) n ; auto with coc.
  eapply wf_var with s ; auto with coc.
Qed.

Lemma gen_sorting_var : 
  forall e n s, e |- Ref n : Srt s -> is_prop s.
Proof.
  intros.
  apply gen_sorting_var_aux with e (Ref n) (Srt s) n ; auto.
Qed.

Lemma gen_sorting_app_aux : forall e t Ts, e |- t : Ts ->
  forall M N, t = App M N ->
  forall s, Ts = Srt s -> is_prop s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  inversion_clear H1.
  pose (type_no_kind_prod_type H0).
  induction s ; unfold is_prop ; simpl ; auto.
  pose (subst_to_sort _ H2 (typ_not_kind H)).
  rewrite e0 in t.
  simpl in t ; contradiction.

  rewrite H4 in H0.
  pose (typ_sort H0).
  intuition.
Qed.

Lemma gen_sorting_app : forall e M N s, e |- App M N : Srt s -> is_prop s.
Proof.
  intros.
  eapply gen_sorting_app_aux with e (App M N) (Srt s) M N ; auto ; auto.
Qed.

Lemma sorting_lambda_aux : forall e t Ts, e |- t : Ts ->
  forall T M, t = Abs T M -> forall s, Ts <> Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  unfold not ; intros.
  rewrite H4 in H0.
  destruct (typ_sort H0).
  inversion H6.
  rewrite H8 in H2.
  rewrite H4 in H2.
  pose (coerce_propset_r H2).
  pose (IHtyp1 T M H3 s0).
  contradiction.
Qed.
(*
Lemma sorting_lambda_range_aux : forall e t Ts, e |- t : Ts ->
  forall T M, t = Abs T M -> forall s, type_range Ts <> Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  unfold not ; intros.

  induction U ; simpl ; intros ; try discriminate.
  simpl in H3.
  assert(e |- Abs T M : Prod T (Srt s0)).
  apply type_abs with s1 s2 ; auto.
  pose (sorting_lambda_aux 



  destruct (typ_sort _ _ _ H0).
  

  rewrite H4 in H0.
  destruct (typ_sort _ _ _ H0).
  inversion H6.
  rewrite H8 in H2.
  rewrite H4 in H2.
  pose (coerce_propset_r H2).
  pose (IHtyp1 T M H3 s0).
  contradiction.
Qed.
*)
Lemma sorting_lambda : forall e T M s, ~ e |- Abs T M : Srt s.
Proof.
  unfold not ; intros.
  apply (sorting_lambda_aux H (refl_equal (Abs T M)) (refl_equal (Srt s))).
Qed.

Lemma generation_prod_aux : forall e T Ts, e |- T : Ts ->
  forall U V, T = Prod U V -> exists s, Ts = Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  exists s2 ; auto.

  destruct (IHtyp1 U0 V0 H3).
  rewrite H4 in H1.
  induction (typ_sort H1).
  inversion H6.
  rewrite H8 in H2.
  rewrite H4 in H2.
  pose (coerce_propset_l H2).
  exists x ; auto.
Qed.

Lemma generation_prod : forall e U V Ts, e |- Prod U V : Ts ->
  exists s, Ts = Srt s.
Proof.
  intros.
  eapply generation_prod_aux with e (Prod U V) U V ; auto.
Qed.

Lemma generation_prod2_aux : forall e T Ts, e |- T : Ts ->
  forall U V, T = Prod U V -> forall s, Ts = Srt s ->
  (exists s', e |- U : Srt s') /\ (U :: e) |- V : Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  inversion H1.
  rewrite H4 in H.
  rewrite H5 in H0.
  rewrite H4 in H0.

  split.
  exists s1 ; auto.
  inversion H2.
  rewrite <- H6.
  assumption.

  rewrite H4 in H2.
  rewrite H4 in H0.
  induction (typ_sort H0).
  inversion H6.
  rewrite H8 in H2.
  pose (coerce_propset_r H2).

  apply (IHtyp1 U0 V0 H3 s0 e0).
Qed.

Lemma generation_prod2 : forall e U V s, e |- Prod U V : Srt s ->
  (exists s', e |- U : Srt s') /\ (U :: e) |- V : Srt s.
Proof.
  intros.
  eapply generation_prod2_aux  ; auto ; auto.
Qed.

Lemma generation_sum_aux : forall e T Ts, e |- T : Ts ->
  forall U V, T = Sum U V -> exists s, Ts = Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  exists s3 ; auto.

  destruct (IHtyp1 U0 V0 H3).
  rewrite H4 in H1.
  induction (typ_sort H1).
  inversion H6.
  rewrite H8 in H2.
  rewrite H4 in H2.
  pose (coerce_propset_l H2).
  exists x ; auto.
Qed.

Lemma generation_sum : forall e U V Ts, e |- Sum U V : Ts ->
  exists s, Ts = Srt s.
Proof.
  intros.
  eapply generation_sum_aux with e (Sum U V) U V ; auto.
Qed.

Lemma generation_sum2_aux : forall e T Ts, e |- T : Ts ->
  forall U V, T = Sum U V -> forall s, Ts = Srt s -> 
  exists s', e |- U : Srt s' /\ exists s'', (U :: e) |- V : Srt s'' /\ sum_sort s' s'' s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  inversion H2.
  rewrite <- H6.
  rewrite <- H5.

  exists s1 ; intuition.
  exists s2 ; intuition.
  inversion H3 ; auto.
  rewrite <- H7 ; auto.

  rewrite H4 in H2.
  pose (coerce_propset_r H2).

  apply (IHtyp1 U0 V0 H3 s0 e0) ; auto.
Qed.

Lemma generation_sum2 : forall e U V s, e |- Sum U V : Srt s ->
  exists s', e |- U : Srt s' /\ exists s'', (U :: e) |- V : Srt s'' /\ sum_sort s' s'' s.
Proof.
  intros.
  eapply generation_sum2_aux  ; auto ; auto.
Qed.

Lemma generation_subset_aux : forall e T Ts, e |- T : Ts ->
  forall U V, T = Subset U V -> Ts = Srt set.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  auto.

  pose (IHtyp1 U0 V0 H3).
  rewrite e0 in H2.
  exact (coerce_propset_l H2).
Qed.

Lemma generation_subset : forall e U V Ts, e |- Subset U V : Ts ->
  Ts = Srt set.
Proof.
  intros.
  eapply generation_subset_aux with e (Subset U V) U V ; auto.
Qed.

Lemma generation_subset2_aux : forall e T Ts, e |- T : Ts ->
  forall U V, T = Subset U V -> Ts = Srt set ->
  e |- U : Srt set /\ (U :: e) |- V : Srt prop.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  inversion H1.
  rewrite H4 in H.
  rewrite H5 in H0.
  rewrite H4 in H0.
  intuition.

  rewrite H4 in H2.
  pose (coerce_propset_r H2).
 
  apply (IHtyp1 U0 V0 H3 e0).
Qed.

Lemma generation_subset2 : forall e U V s, e |- Subset U V : Srt set ->
  (e |- U : Srt set) /\ (U :: e) |- V : Srt prop.
Proof.
  intros.
  eapply generation_subset2_aux  ; auto ; auto.
Qed.

Lemma var_sort_item : forall e t T, e |- t : T ->
  forall n, t = Ref n -> 
  forall s, T = (Srt s) -> item _ (Srt s) e n.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  inversion H1.

  rewrite H2 in H0.
  rewrite <- H4 ; auto.
  destruct H0.
  assert(x = Srt s).
  apply (inv_lift_sort) with (S n) ; auto.
  rewrite H5 in H3 ; assumption.

  rewrite H4 in H2.
  pose (coerce_propset_r H2).
  pose (IHtyp1 n H3 s0 e0).
  assumption.
Qed. 

Lemma no_sort_type_range : forall A, no_sort A -> forall s, type_range A <> Srt s.
Proof.
  induction A ; simpl ; intros ; intuition ; try discriminate ; auto.
  apply H1 with s ; auto.
  apply H3 with s ; auto.
Qed.

Lemma is_low_type_range : forall A, forall e T, e |- A : T -> is_low_full A -> 
  (forall s, type_range A <> Srt s) \/ 
  (exists s, type_range A = Srt s /\ is_prop s).
Proof.
  induction A ;  simpl ; intros ; intuition ; try discriminate.

  right.
  exists s ; intuition.
  
  destruct (generation_prod H).
  rewrite H1 in H.
  destruct (generation_prod2 H).
  apply IHA2 with (A1 :: e) (Srt x) ; auto.
  
  destruct (generation_sum H).
  rewrite H1 in H.
  destruct (generation_sum2 H).
  destruct H3.
  destruct H4.
  destruct H4.
  apply IHA2 with (A1 :: e) (Srt x1) ; auto.

  left.
  intros.
  pose (no_sort_type_range _ H2 H0).
  contradiction.

  destruct (generation_sum H).
  rewrite H0 in H.
  destruct (generation_sum2 H).
  destruct H3.
  destruct H4.
  destruct H4.
  apply IHA2 with (A1 :: e) (Srt x1) ; auto.
Qed.

Definition is_low_sort t : Prop := t = Srt prop \/ t = Srt set.

Lemma conv_is_low_range : forall A s, conv (Srt s) A -> 
  is_low_sort (type_range A) -> A = Srt s.
Proof.
  induction A ; simpl ; intros ; 
  try unfold is_low_sort in H0 ; intuition ; try discriminate ; auto with coc core datatypes.
  
  rewrite (conv_sort _ _ H).
  auto.

  rewrite (conv_sort _ _ H).
  auto.

  elim conv_sort_prod with s A1 A2 ; auto with coc core.
  elim conv_sort_prod with s A1 A2 ; auto with coc core.

  elim conv_sort_sum with s A1 A2 ; auto with coc core.
  elim conv_sort_sum with s A1 A2 ; auto with coc core.
Qed.

Lemma conv_is_low_dom : forall A s, conv (Srt s) A -> 
  is_low_sort (type_dom A) -> A = Srt s.
Proof.
  induction A ; simpl ; intros ; 
  try unfold is_low_sort in H0 ; intuition ; try discriminate ; auto with coc core datatypes.
  
  rewrite (conv_sort _ _ H).
  auto.

  rewrite (conv_sort _ _ H).
  auto.

  elim conv_sort_prod with s A1 A2 ; auto with coc core.
  elim conv_sort_prod with s A1 A2 ; auto with coc core.

  elim conv_sort_sum with s A1 A2 ; auto with coc core.
  elim conv_sort_sum with s A1 A2 ; auto with coc core.
Qed.
 
Lemma conv_is_low_range_full : forall A B, conv A B ->
  is_low_sort (type_range A) -> 
  is_low_sort (type_range B) -> type_range A = type_range B.
Proof.
  induction A ; simpl ; intros ; 
  try unfold is_low_sort in H0 ;   
  intuition ; try discriminate ; auto with coc core datatypes.
  
  rewrite (conv_is_low_range H H1).
  simpl ; auto.

  rewrite (conv_is_low_range H H1).
  simpl ; auto.
  
  induction B ; simpl ; intros ; 
  try unfold is_low_sort in H1 ;   
  intuition ; try discriminate ; auto with coc core datatypes.

  elim conv_sort_prod with s A1 A2 ; auto with coc core.
  elim conv_sort_prod with s A1 A2 ; auto with coc core.

  simpl in H0.
  apply (IHA2 B2 (inv_conv_prod_r _ _ _ _ H)).
  unfold is_low_sort ; rewrite H2 ; auto.
  unfold is_low_sort ; rewrite H0 ; auto.

  simpl in H0.
  apply (IHA2 B2 (inv_conv_prod_r _ _ _ _ H)).
  unfold is_low_sort ; rewrite H2 ; auto.
  unfold is_low_sort ; rewrite H0 ; auto.

  elim conv_prod_sum with A1 A2 B1 B2 ; auto with coc.
  elim conv_prod_sum with A1 A2 B1 B2 ; auto with coc.

  induction B ; simpl ; intros ; 
  try unfold is_low_sort in H1 ;   
  intuition ; try discriminate ; auto with coc core datatypes.

  elim conv_sort_prod with s A1 A2 ; auto with coc core.
  elim conv_sort_prod with s A1 A2 ; auto with coc core.

  simpl in H0.
  apply (IHA2 B2 (inv_conv_prod_r _ _ _ _ H)).
  unfold is_low_sort ; rewrite H2 ; auto.
  unfold is_low_sort ; rewrite H0 ; auto.

  simpl in H0.
  apply (IHA2 B2 (inv_conv_prod_r _ _ _ _ H)).
  unfold is_low_sort ; rewrite H2 ; auto.
  unfold is_low_sort ; rewrite H0 ; auto.

  elim conv_prod_sum with A1 A2 B1 B2 ; auto with coc.
  elim conv_prod_sum with A1 A2 B1 B2 ; auto with coc.

  induction B ; simpl ; intros ; 
  try unfold is_low_sort in H1 ;   
  intuition ; try discriminate ; auto with coc core datatypes.

  elim conv_sort_sum with s A1 A2 ; auto with coc core.
  elim conv_sort_sum with s A1 A2 ; auto with coc core.

  elim conv_prod_sum with B1 B2 A1 A2; auto with coc core.
  elim conv_prod_sum with B1 B2 A1 A2; auto with coc core.

  simpl in H0.
  apply (IHA2 B2 (inv_conv_sum_r _ _ _ _ H)).
  unfold is_low_sort ; rewrite H2 ; auto.
  unfold is_low_sort ; rewrite H0 ; auto.

  simpl in H0.
  apply (IHA2 B2 (inv_conv_sum_r _ _ _ _ H)).
  unfold is_low_sort ; rewrite H2 ; auto.
  unfold is_low_sort ; rewrite H0 ; auto.

  induction B ; simpl ; intros ; 
  try unfold is_low_sort in H1 ;   
  intuition ; try discriminate ; auto with coc core datatypes.

  elim conv_sort_sum with s A1 A2 ; auto with coc core.
  elim conv_sort_sum with s A1 A2 ; auto with coc core.

  elim conv_prod_sum with B1 B2 A1 A2; auto with coc core.
  elim conv_prod_sum with B1 B2 A1 A2; auto with coc core.

  simpl in H0.
  apply (IHA2 B2 (inv_conv_sum_r _ _ _ _ H)).
  unfold is_low_sort ; rewrite H2 ; auto.
  unfold is_low_sort ; rewrite H0 ; auto.

  simpl in H0.
  apply (IHA2 B2 (inv_conv_sum_r _ _ _ _ H)).
  unfold is_low_sort ; rewrite H2 ; auto.
  unfold is_low_sort ; rewrite H0 ; auto.
Qed.

Lemma conv_is_low_dom_full : forall A B, conv A B ->
  is_low_sort (type_dom A) -> 
  is_low_sort (type_dom B) -> type_dom A = type_dom B.
Proof.
  induction A ; simpl ; intros ; 
  try unfold is_low_sort in H0 ;   
  intuition ; try discriminate ; auto with coc core datatypes.
  
  rewrite (conv_is_low_dom H H1).
  simpl ; auto.

  rewrite (conv_is_low_dom H H1).
  simpl ; auto.
  
  induction B ; simpl ; intros ; 
  try unfold is_low_sort in H1 ;   
  intuition ; try discriminate ; auto with coc core datatypes.

  elim conv_sort_sum with s A1 A2 ; auto with coc core.
  elim conv_sort_sum with s A1 A2 ; auto with coc core.

  simpl in H0.
  apply (conv_is_low_range_full (inv_conv_sum_l _ _ _ _ H)).
  rewrite H2 ; unfold is_low_sort ; auto.
  rewrite H0 ; unfold is_low_sort ; auto.

  simpl in H0.
  apply (conv_is_low_range_full (inv_conv_sum_l _ _ _ _ H)).
  unfold is_low_sort ; rewrite H2 ; try rewrite H0 ; auto.
  unfold is_low_sort ; try rewrite H0 ; auto.

  induction B ; simpl ; intros ; 
  try unfold is_low_sort in H1 ;   
  intuition ; try discriminate ; auto with coc core datatypes.

  elim conv_sort_sum with s A1 A2 ; auto with coc core.
  elim conv_sort_sum with s A1 A2 ; auto with coc core.

  simpl in H0.
  apply (conv_is_low_range_full (inv_conv_sum_l _ _ _ _ H)).
  rewrite H2 ; unfold is_low_sort ; auto.
  rewrite H0 ; unfold is_low_sort ; auto.

  simpl in H0.
  apply (conv_is_low_range_full (inv_conv_sum_l _ _ _ _ H)).
  unfold is_low_sort ; rewrite H2 ; try rewrite H0 ; auto.
  unfold is_low_sort ; try rewrite H0 ; auto.
Qed.


Lemma term_type_range_kinded : forall e t T, e |- t : T ->
  forall s, type_range t = Srt s -> T = Srt kind. 
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  
  apply IHtyp2 with s ; auto.
  pose (IHtyp2 s H2) ; auto.
  inversion e0.
  rewrite H4 in H1.
  destruct H1 ; intuition ; try discriminate.
  rewrite H6 ; auto.
  
  rewrite (IHtyp1 _ H3) in H1.
  elim typ_not_kind2 with e (Srt s) ; auto.
Qed.

Lemma term_type_range_not_kind : forall e t T, e |- t : T ->
  forall s, type_range t = Srt s -> s <> kind. 
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  
  inversion H0.
  unfold not ; intros ; discriminate.
  inversion H0.
  unfold not ; intros ; discriminate.
Qed.


Lemma term_type_dom_kinded : forall e t T, e |- t : T ->
  forall s, type_dom t = Srt s -> T = Srt kind. 
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
 
  pose (term_type_range_kinded H H2).
  inversion e0.
  rewrite H4 in H1.
  destruct H1 ; intuition ; try discriminate.
  rewrite H6 ; auto.
  
  rewrite (IHtyp1 _ H3) in H1.
  elim typ_not_kind2 with e (Srt s) ; auto.
Qed.

Lemma is_prop_is_low_sort : forall s, is_prop s -> is_low_sort (Srt s).
Proof.
  intros.
  destruct H ; unfold is_low_sort ; intuition.
  rewrite H ; auto.
  rewrite H ; auto.
Qed.


Lemma conv_sum_ref : forall U V n, ~ conv (Sum U V) (Ref n).
Admitted.
Lemma conv_prod_ref : forall U V n, ~ conv (Prod U V) (Ref n).
Admitted.
Lemma conv_sum_pair : forall U V T u v, ~ conv (Sum U V) (Pair T u v).
Admitted.
Lemma conv_prod_pair : forall U V T u v, ~ conv (Prod U V) (Pair T u v).
Admitted.
Lemma conv_prod_abs : forall U V M N, ~ conv (Prod U V) (Abs M N).
Admitted.



Lemma conv_dom : forall e A Ts, e |- A : Ts -> 
  forall B s s', Ts = Srt s -> 
  e |- B : Srt s ->
  conv A B -> (type_dom A = Srt s' -> type_dom B = Srt s')
  /\ (type_range A = Srt s' -> type_range B = Srt s')
  .
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  inversion H0.
  rewrite <- H4 in H1.
  pose (sort_conv_eq H1 (sym_conv _ _ H2)).
  rewrite e0.
  simpl.
  auto.

  inversion H0.
  rewrite <- H4 in H1.
  pose (sort_conv_eq H1 (sym_conv _ _ H2)).
  rewrite e0.
  simpl.
  auto.

  split ; intros ; discriminate.

  split ; intros ; discriminate.

  split ; intros ; try discriminate.

  induction B ; simpl ; intros ; try discriminate.
  
  elim conv_sort_prod with s0 T U ; auto with coc.
  elim conv_prod_ref with T U n ; auto with coc.
  elim conv_prod_abs with T U B1 B2 ; auto with coc.

  pose (term_type_range_kinded H0 H4).
  rewrite H1 in e0.
  inversion e0.
  rewrite H6 in H2.
  pose (gen_sorting_app H2).
  destruct i ; discriminate.
  elim conv_prod_pair with T U B1 B2 B3 ; auto.

  destruct (IHtyp2 B2 s s') ; auto with coc.
  destruct (generation_prod2 H2).
  apply typ_conv_env with (B1 :: e) ; auto with coc core.
  destruct H5.
  apply coerce_env_hd with x.

  pose (IHtyp1 
  apply coerce_conv with B1 B1 ; auto with coc.

Focus 2.
  apply IHtyp1 with s0 ; auto.
  rewrite H3 in H2.
  apply (coerce_propset_r H2).

  pose (term_type_range_kinded H H4).
  
  induction H1 ; intuition.
  rewrite H6 in e0 ; discriminate.

  induction B ; simpl ; intros ; try discriminate.

  elim conv_sort_sum with s0 T U ; auto with coc.

  elim conv_sum_ref with T U n ; auto.

  elim (sorting_lambda H3).

  inversion H2.
  rewrite <- H9 in H3.
  rewrite H8 in H3.
  pose (gen_sorting_app H3).
  destruct i ; discriminate.

  elim conv_sum_pair with T U B1 B2 B3 ; auto.

  elim conv_prod_sum with B1 B2 T U ; auto with coc.
  inversion H2.
  rewrite <- H9 in H3.
  pose (generation_sum2 H3).
  destruct e1 ; intuition.
  destruct H11.
  intuition.
  induction H12 ; intuition ; try discriminate.
  rewrite H8 in H14 ; discriminate.
  rewrite H7 in H10.
  rewrite H1 in IHtyp1.
  pose (IHtyp1 kind (refl_equal (Srt kind)) B1 H10).

  intros.

  


(*
Lemma type_range_conv : forall e T U s, conv T U -> e |- T : Srt kind -> e |- U : Srt kind ->
  forall s0, type_range T = Srt s0 -> type_range U = Srt s0.
Proof.
  intros.
  *)


Lemma type_range_sub : forall e T U s, e |- T >> U : s ->
  forall s0, (type_range U = Srt s0 -> type_range T = Srt s0) /\
  (type_dom U = Srt s0 -> type_dom T = Srt s0).
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  destruct (IHcoerce1 s). 
  destruct (IHcoerce2 s0).
  split ; intros ; auto.
  discriminate.

  destruct (IHcoerce1 s0). 
  destruct (IHcoerce2 s0).
  split ; intros ; auto.

  pose (coerce_sort_r H).
  destruct (IHcoerce s0). 
  split ; intros ; auto.

  pose (term_type_range_kinded t H3).
  discriminate.

  pose (coerce_sort_l H).
  pose (term_type_dom_kinded t H3).
  discriminate.

  split ; intros ; discriminate.
  split ; intros.

  pose (term_type_range_kinded H2 H6).
  inversion e0.
  rewrite H8 in H.
  rewrite H8 in H0.
  rewrite H8 in H1.
  rewrite H8 in H2.
  pose (sort_of_kinded H).
  pose (sort_of_kinded H0).
  pose (sort_of_kinded H1).
  pose (sort_of_kinded H7).
  destruct (is_low_type_range H7 i2).
  pose (H9 s0) ; contradiction.
  do 2 destruct H9.
  
  pose (is_prop_is_low_sort H10).
  rewrite <- H9 in i3.

  destruct (is_low_type_range H1 i1).
  
  
Focus 2.
  pose (H9 s0) ; contradiction.
  do 2 destruct H9.
  
  pose (is_prop_is_low_sort H10).
  rewrite <- H9 in i3.

  assert(is_low_sort (type_range D)).
  rewrite H9 ; unfold is_low_sort ; destruct H10 ; simpl ; auto.
  rewrite H10 ; auto.
  rewrite H10 ; auto.


  pose (conv_is_low_range_full H3 H11 i0).
  
  pose (is_low_type_range H0).
  pose (is_low_type_range H0).


  pose (type_kind_range H1).
  pose (type_kind_range H7).
  
  pose (conv_is_low_range_full H5 i1 i2).
  rewrite H6 in e2.
  pose (IHcoerce _ e2).
  rewrite <- e3.
  assumption.
Qed.





Lemma type_dom_sub : forall e T U s, e |- T >> U : s ->
  forall s0, type_dom U = Srt s0 -> type_dom T = Srt s0.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  apply type_range_sub with e A' s ; auto with coc.

  pose (coerce_sort_r H).
  pose (term_type_dom_kinded t H1).
  discriminate.
  
  induction D ; simpl in H6 ; try discriminate.

  destruct (typ_sort H2).
  inversion H8.
  rewrite H10 in H1.
  pose (type_kind_range H1).
  pose (conv_is_low_range (sym_conv _ _ H5) i).
  rewrite e0 in IHcoerce.
  inversion H6.
  assert (type_dom B = Srt s0).
  apply IHcoerce.
  rewrite H11 ; simpl ; auto.

  pose (sort_conv_eq H1 H5).
  rewrite e1 in H4.
  pose (coerce_propset_r H4).
  rewrite e2 in H3.
  rewrite H10 in H.
  pose (sort_conv_eq H H3).
  rewrite e3 ; simpl ; auto.

  pose (generation_sum2 H2).
  destruct e0.
  intuition.
  pose (term_type_range_kinded H8 H6).
  inversion e0.

  pose (term_type_dom_kinded H2 H6).
  inversion e1.

  
  rewrite H8 in H.
  rewrite H8 in H0.
  rewrite H8 in H1.
  rewrite H8 in H2.
  pose (type_kind_dom H).
  pose (type_kind_dom H0).
  pose (type_kind_dom H1).
  pose (type_kind_dom H7 H6).
  


  pose (conv_is_low_dom_full H3).
  pose (conv_is_low_range_full H5 i1 i2).
  rewrite H6 in e2.
  pose (IHcoerce _ e2).
  rewrite <- e3.
  assumption.



  unfold sum_sort in H10.
  intuition.
  rewrite H10 in H6.
  simpl in H9 ; inversion H9.
  
  

  Focus 2.
  

rewrite H10 in H.
  pose (type_kind_range H).
  pose(conv_is_low_range).
  induction i.
  pose (term_type_range_

  pose (conv_is_low_range).
 
  pose (term_type_dom_kinded H2 H6).
  inversion e0.
  rewrite H8 in H.
  rewrite H8 in H0.
  rewrite H8 in H1.
  clear e0.
  rewrite H8 in H2.
  pose (type_kind_dom H2 H6).

  pose (conv_is_low_dom_full).
  
  pose (type_kind_dom H).
  pose (type_kind_range H0).
  pose (type_kind_range H1).
  pose (conv_is_low_dom_full H3 i i0).
  pose (conv_is_low_dom_full H5 i1 i2).
  rewrite H6 in e2.
  pose (IHcoerce _ e2).
  rewrite <- e3.
  assumption.

  induction B ; try discriminate.
  simpl in H2.

  inversion H2.
  induction (typ_sort _ _ _ H0).
  inversion H5.
  rewrite H7 in H.
  pose (kind_is_prod H (refl_equal (Srt kind))).
  rewrite (conv_is_low_range (sym_conv _ _ H1) i).
  simpl ; assumption.

  rewrite <- H2.
  simpl in H2.
  destruct (generation_prod2 H0).
  induction H3.
  pose (term_type_range_kinded H3 H2).
  inversion e0.
  rewrite H6 in H3.

  simpl.
  rewrite H2.
  
  pose (conv_is_low_dom_full).

Focus 4.
  pose (coerce_sym _ _ _ _ H).
  exact (type_range_sub c H5).

Focus 4.
  exact (type_range_sub H H5).

Focus 4.
  pose (IHcoerce _ H1).
  pose (coerce_sort_l _ _ _ _ H).
  pose (term_type_range_kinded t e0).
  

  induction A ; try discriminate.
  
  elim conv_sort_prod with s1 B1 B2 ; auto.
  elim conv_ref_prod with n B1 B2 ; auto.
  elim conv_abs_prod with A1 A2 B1 B2 ; auto.
  simpl.
  

  apply IHB1.


  apply (conv_is_low_dom_full H1).
  

apply kind_is_prod with e (Srt s) ; auto.
  apply kind_is_prod with e (Srt s) ; auto.

  rewrite <- H2.
  pose (term_type_range_kinded H0 H2).
  inversion e0.
  rewrite H4 in H0.
  
  apply (conv_is_low_range_full H1).
  apply kind_is_prod with e (Srt s) ; auto.
  apply kind_is_prod with e (Srt s) ; auto.

  pose (coerce_sort_r _ _ _ _ H).
  pose (term_type_range_kinded t H1).
  discriminate.
Qed.

Lemma var_sort_dom_item : forall e n T, e |- Ref n : T ->
  forall s, type_dom T = (Srt s) -> 
  exists T', item_lift T' e n /\ type_dom T' = Srt s.
Admitted.

Lemma unique_var_dom_sort : forall e n T, e |- Ref n : T ->
  forall s, type_dom T = Srt s ->
  forall T', e |- Ref n : T' -> 
  forall s', type_dom T' = Srt s' -> s = s'.
Proof.
  intros.
  destruct (var_sort_dom_item H H0).
  destruct (var_sort_dom_item H1 H2).
  destruct H3 ; destruct H4.
  destruct H3 ; destruct H4.
  pose (fun_item _ _ _ _ _ H7 H8).
  rewrite <- e0 in H4.
  rewrite <- H4 in H3.
  rewrite <- H3 in H6.
  rewrite H6 in H5.
  inversion H5.
  auto.
Qed.
*)
Lemma var_sort_range_item_aux : forall e t T, e |- t : T ->
  forall n, t = Ref n -> 
  forall s, type_range T = (Srt s) -> 
  exists T', item_lift T' e n /\ type_range T' = Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  inversion H1.
  
  induction T ; simpl ; simpl in H2 ; try discriminate.
  
  rewrite H2 in H0.
  rewrite <- H4 ; auto.
  destruct H0.
  assert(x = Srt s).
  apply (inv_lift_sort) with (S n) ; auto.
  inversion H2.
  exists (Srt s).
  simpl ; intuition ; auto.
  exists (Srt s) ; unfold lift ; simpl ; auto.
  rewrite H5 in H3 ; assumption.
  
  inversion H1.
  exists (Prod T1 T2).
  intuition ; auto.
  rewrite <- H5 ; assumption.
  
  inversion H1.
  exists (Sum T1 T2).
  intuition ; auto.
  rewrite <- H5 ; assumption.

  exact (IHtyp1 n H3 s0 (type_range_sub H2 H4)).
Qed. 

Lemma var_sort_range_item : forall e n T, e |- Ref n : T ->
  forall s, type_range T = (Srt s) -> 
  exists T', item_lift T' e n /\ type_range T' = Srt s.
Proof.
  intros.
  eapply var_sort_range_item_aux with (Ref n) T; auto ; auto.
Qed.


Lemma unique_var_sort : forall e n s, e |- Ref n : Srt s ->
  forall s', e |- Ref n : Srt s' -> s = s'.
Proof.
  intros.
  pose (var_sort_item H (refl_equal (Ref n)) (refl_equal (Srt s))).
  pose (var_sort_item H0 (refl_equal (Ref n)) (refl_equal (Srt s'))).
  pose (fun_item _ _ _ _ _ i i0).
  inversion e0 ; auto.
Qed.

Lemma unique_var_range_sort : forall e n T, e |- Ref n : T ->
  forall s, type_range T = Srt s ->
  forall T', e |- Ref n : T' -> 
  forall s', type_range T' = Srt s' -> s = s'.
Proof.
  intros.
  destruct (var_sort_range_item H H0).
  destruct (var_sort_range_item H1 H2).
  destruct H3 ; destruct H4.
  destruct H3 ; destruct H4.
  pose (fun_item _ _ _ _ _ H7 H8).
  rewrite <- e0 in H4.
  rewrite <- H4 in H3.
  rewrite <- H3 in H6.
  rewrite H6 in H5.
  inversion H5.
  auto.
Qed.

Lemma subst_sort : forall t t' n s, subst_rec t t' n = Srt s -> 
  t = Srt s \/ t' = Srt s.
Proof.
  induction t' ;  simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  generalize H.
  elim (lt_eq_lt_dec n0 n).
  intros a ; case a ; clear a ; intros ; try discriminate ; auto.
  left.
  exact (inv_lift_sort _ _ H0).

  intros.
  discriminate.
Qed.

Lemma sort_of_app_aux : forall e t Ts, e |- t : Ts ->
  forall M N, t = App M N ->
  forall s, Ts = Srt s ->
  (exists V, e |- M : Prod V (Srt s)) \/ N = Srt s.
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  inversion H1.

  induction (subst_sort _ _ _ H2).
  rewrite <- H5.
  right ; auto.
  
  rewrite H3 in H0.
  rewrite H4 in H0.
  left ; exists V ; auto.

  rewrite H4 in H2.
  pose (coerce_propset_r H2).
  exact (IHtyp1 _ _ H3 _ e0).
Qed.

Lemma sort_of_app : forall e M N s, e |- App M N : Srt s ->
  (exists V, e |- M : Prod V (Srt s)) \/ N = Srt s.
Proof.
  intros. 
  eapply sort_of_app_aux ; auto ; auto.
Qed.

Lemma type_range_lift : forall n t k s, type_range (lift_rec n t k) = Srt s -> 
  type_range t = Srt s.
Proof.
  induction t ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  generalize H ; clear H.
  elim (le_gt_dec k n0) ;  simpl ; intros ; try discriminate.
  apply IHt2 with (S k) ; auto.
  apply IHt2 with (S k) ; auto.
Qed.

Lemma type_range_subst : forall t u n s, type_range (subst_rec t u n) = Srt s ->
  type_range t = Srt s \/ type_range u = Srt s.
Proof.
  induction u ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  generalize H.
  elim (lt_eq_lt_dec n0 n) ; simpl ; try (intros ; discriminate).
  intro a ; case a ; clear a ; simpl ; intros ; try discriminate.
  unfold lift in H0.
  left ; exact (type_range_lift _ _ _ H0).
  
  apply IHu2 with (S n) ; auto.
  apply IHu2 with (S n) ; auto.
Qed.

Lemma sort_of_app_range_aux : forall e t Ts, e |- t : Ts ->
  forall M N, t = App M N ->
  forall s, type_range Ts = Srt s ->
  exists V, exists T,  e |- N : V /\ e |- M : Prod V T /\
  (type_range T = (Srt s) \/ type_range N = Srt s).
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  inversion H1.

  induction (type_range_subst _ _ _ H2).
  rewrite <- H5.
  exists V.
  exists Ur.
  rewrite <- H4.
  split ; auto.
  
  exists V ; auto.
  exists Ur.
  rewrite <- H5.
  rewrite <- H4.
  split ; auto.
  
  pose (type_range_sub H2 H4).
  exact (IHtyp1 _ _ H3 _ e0).
Qed.

Lemma sort_of_app_range : forall e M N Ts, e |- App M N : Ts ->
  forall s, type_range Ts = Srt s ->
  exists V, exists T,  e |- N : V /\ e |- M : Prod V T /\
  (type_range T = (Srt s) \/ type_range N = Srt s).
Proof.
  intros. 
  apply sort_of_app_range_aux with (App M N) Ts  ; auto ; auto.
Qed.

Lemma sort_of_abs_range_aux : forall e t Ts, e |- t : Ts ->
  forall M N, t = Abs M N ->
  forall s, type_range Ts = Srt s ->
  exists s1, exists s2, exists T, e |- M : (Srt s1) /\ M :: e |- N : T /\
  M :: e |- T : Srt s2 /\ type_range T = (Srt s).
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  exists s1 ; exists s2.
  exists U.
  inversion H2.
  rewrite <- H5 ; rewrite <- H6.
  intuition.

  apply (IHtyp1) ; auto.
  
  apply (type_range_sub H2 H4).
Qed.

Lemma sort_of_abs_range : forall e M N Ts, e |- Abs M N : Ts ->
  forall s, type_range Ts = Srt s ->
  exists s1, exists s2, exists T, e |- M : (Srt s1) /\ M :: e |- N : T /\
  M :: e |- T : Srt s2 /\ type_range T = (Srt s).
Proof.
  intros. 
  apply sort_of_abs_range_aux with (Abs M N) Ts  ; auto ; auto.
Qed.

(*
Lemma sort_of_abs_dom_aux : forall e t Ts, e |- t : Ts ->
  forall M N, t = Abs M N ->
  forall s, type_dom Ts = Srt s ->
  exists s1, exists s2, exists T, e |- M : (Srt s1) /\ M :: e |- N : T /\
  M :: e |- T : Srt s2 /\ type_dom (Prod M T) = (Srt s).
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  exists s1 ; exists s2.
  exists U.
  inversion H2.
  rewrite <- H5 ; rewrite <- H6.
  intuition.

  simpl in IHtyp1 ; auto.
  apply IHtyp1 ; auto.
  apply (type_range_sub H2 H4).
Qed.


Lemma sort_of_abs_range : forall e M N Ts, e |- Abs M N : Ts ->
  forall s, type_range Ts = Srt s ->
  exists s1, exists s2, exists T, e |- M : (Srt s1) /\ M :: e |- N : T /\
  M :: e |- T : Srt s2 /\ type_range T = (Srt s).
Proof.
  intros. 
  apply sort_of_abs_range_aux with (Abs M N) Ts  ; auto ; auto.
Qed.

*)


Lemma sort_of_pair_range_aux : forall e t Ts, e |- t : Ts ->
  forall T u v, t = Pair T u v ->
  forall s, type_range Ts = Srt s ->
  exists U, exists V, exists s1, exists s2,
  T = Sum U V /\
  e |- u : U /\ e |- U : Srt s1 /\ U :: e |- V : Srt s2 /\
  e |- v : subst u V /\ e |- Sum U V : Srt s2 /\ 
  type_range V = (Srt s).
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  exists U ; exists V ; exists s1 ; exists s2.
  inversion H4.
  rewrite <- H9 ; rewrite <- H8.
  intuition.
  apply type_sum with s1 ; auto.

  apply IHtyp1 ; auto.
  apply (type_range_sub H2 H4).
Qed.

Lemma sort_of_pair_range : forall e T u v Ts, e |- Pair T u v : Ts ->
  forall s, type_range Ts = Srt s ->
  exists U, exists V, exists s1, exists s2,
  T = Sum U V /\
  e |- u : U /\ e |- U : Srt s1 /\ U :: e |- V : Srt s2 /\
  e |- v : subst u V /\ e |- Sum U V : Srt s2 /\ 
  type_range V = (Srt s).
Proof.
  intros. 
  apply sort_of_pair_range_aux with (Pair T u v) Ts  ; auto ; auto.
Qed.

Lemma strength_sort_judgement : forall T e s s', T :: e |- Srt s : Srt s' ->
  e |- Srt s : Srt s'.
Proof.
  intros.
  pose (typ_wf H).
  inversion w.
  pose (typ_wf H1).
  inversion H ; auto with coc.

  destruct (typ_sort H).
  inversion H11.
  rewrite H13 in H4.
  pose (type_has_no_kind H4).
  simpl in t0.
  intuition.
Qed.

Lemma type_sorted : forall e t T, e |- t : T ->
  T = Srt kind \/ exists s, e |- T : Srt s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc ; try discriminate ; 
 try (destruct H ; discriminate) ;  try (destruct H1 ; discriminate).

  right; exact (wf_sort_lift H H0).
 
  right.
  exists s2.
  apply type_prod with s1 ; auto.

  induction IHtyp2 ; try discriminate.
  induction H1.
  induction IHtyp1.
  rewrite H2 in H0.
  pose (type_no_kind_prod_type2 H0).
  simpl in t.
  intuition.

  induction H2.
  right.
  exists x.
  induction (generation_prod2 H1).
  replace (Srt x) with (subst v (Srt x)).
  apply (substitution H4 H).
  unfold subst ; unfold subst_rec ; auto.

  right.
  exists s2.
  apply type_sum with s1 ; auto.

  induction IHtyp2.
  left ; assumption.
  induction H1.
  right.
  exists x ; auto.
  eapply strength_sort_judgement with T ; auto.
  
  induction IHtyp2.
  left ; auto.
  induction H2.
  right ; exists x ; auto.
  eapply strength_sort_judgement with T ; auto.

  induction IHtyp ; try discriminate.
  induction H0.
  induction (generation_sum2 H0).
  destruct H1.
  right ; exists x0 ; auto.

  induction IHtyp ; try discriminate.
  induction H0.
  induction (generation_sum2 H0).
  destruct H1.
  destruct H2.
  right.
  exists x.
  assert (e |- Pi1 t : U).
  apply type_pi1 with V ; auto.
  replace (Srt x) with (subst (Pi1 t) (Srt x)).
  apply (substitution H2 H4).
  unfold subst ; unfold subst_rec ; auto.
  
  right ; exists s ; auto.
Qed.

Lemma sort_of_pi1_range_aux : forall e t Ts, e |- t : Ts ->
  forall u, t = Pi1 u ->
  forall s, type_range Ts = Srt s ->
  exists U, exists V, exists s2, 
  e |- u : Sum U V /\ type_range U = (Srt s)
  /\ sum_sort U V s s2.
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  
  induction (type_sorted H) ; try discriminate.
  induction H2.
  induction (generation_sum2 H2).

  exists U ; exists V.
  inversion H0.
  rewrite <- H5.
  exists x.
  intuition.
  pose (term_type_range_kinded H4 H1).
  inversion e0.
  rewrite H8 in H7.
  unfold sum_sort in H7.
  destruct H7.
  induction H6 ; try discriminate.
  unfold sum_sort.
  intuition.
  
  destruct H6.
  discriminate.

  apply IHtyp1 ; auto.
  apply (type_range_sub H2 H4).
Qed.

Lemma sort_of_pi1_range :  forall e t Ts, e |- Pi1 t : Ts ->
  forall s, type_range Ts = Srt s ->
  exists U, exists V, exists s2, e |- t : Sum U V /\ type_range U = (Srt s)
  /\ sum_sort U V s s2.
Proof.
  intros. 
  apply sort_of_pi1_range_aux with (Pi1 t) Ts  ; auto ; auto.
Qed.

Lemma sort_of_pi2_range_aux : forall e t Ts, e |- t : Ts ->
  forall u, t = Pi2 u ->
  forall s, type_range Ts = Srt s ->
  exists U, exists V, exists s1, 
	e |- u : Sum U V /\ type_range (subst (Pi1 u) V) = (Srt s)
	/\ sum_sort U V s1 s.
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  induction (type_sorted H) ; try discriminate.
  induction H2.
  induction (generation_sum2 H2).

  exists U ; exists V.
  inversion H0.
  rewrite <- H5.
  exists x0.
  intuition.

  unfold sum_sort in H7 |- *.
  destruct H7.
  left ; intuition.
  right.
  split ; intuition.
  
  induction (type_range_subst _ _ _ H1).
  simpl in H6.
  discriminate.

  pose (term_type_range_kinded H3 H6).
  inversion e0.
  rewrite H10 in H8.
  discriminate.
  
  apply IHtyp1 ; auto.
  apply (type_range_sub H2 H4).
Qed.

Lemma sort_of_pi2_range :  forall e t Ts, e |- Pi2 t : Ts ->
  forall s, type_range Ts = Srt s ->
  exists U, exists V, exists s1, e |- t : Sum U V /\ type_range (subst (Pi1 t) V) = (Srt s)
  /\ sum_sort U V s1 s.
Proof.
  intros. 
  apply sort_of_pi2_range_aux with (Pi2 t) Ts  ; auto ; auto.
Qed.

Lemma sort_of_letin_range_aux : forall e t Ts, e |- t : Ts ->
  forall u v, t = Let_in u v ->
  forall s, type_range Ts = Srt s ->
  exists U, exists V, 
  e |- u : U /\ U :: e |- v : V /\ 
  type_range (subst u V) = (Srt s).
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
  (*
  exists U ; exists M.
  inversion H3.
  rewrite <- H6 ; rewrite <- H7.
  intuition.
  *)
  apply IHtyp1 ; auto.
  apply (type_range_sub H2 H4).
Qed.

Lemma sort_of_letin_range :  forall e u v Ts, e |- Let_in u v : Ts ->
  forall s, type_range Ts = Srt s ->
  exists U, exists V,
  e |- u : U /\ U :: e |- v : V /\
  type_range (subst u V) = (Srt s).
Proof.
  intros. 
  apply sort_of_letin_range_aux with (Let_in u v) Ts  ; auto ; auto.
Qed.

Lemma type_range_subst2 : forall t u n s, type_range t = Srt s -> 
  type_range (subst_rec u t n) = Srt s.
Proof.
  induction t ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.
Qed.
