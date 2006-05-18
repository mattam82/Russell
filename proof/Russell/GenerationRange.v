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
Require Import CCPD.Generation.
Require Import CCPD.Axioms.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

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

(*
Lemma gen_sorting_app2_aux : forall e t Ts, e |- t : Ts ->
  forall M N, t = App M N -> forall s, type_range Ts = Srt s -> is_prop s /\ 
  forall Ts', e |- t : Ts' -> type_range Ts' = Srt s.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.

  inversion H1.
  pose (type_no_kind_prod_type H0).
  induction s ; unfold is_prop ; simpl ; auto.
  unfold subst in H2.
  induction (type_range_subst _ _ _ H2).
  pose (term_type_range_not_kind).
  rewrite e0 in t.
  simpl in t ; contradiction.

  split ; auto ; intros.
  rewrite <- H4 in H3 ; rewrite <- H5 in H3.
  induction (sort_of_app H3).
  destruct H6.
  
  pose (gen_sorting_app H1).
  induction s' ; unfold is_prop in i ; intuition ; try discriminate ; auto.
  induction H4.
  
  inversion H1.
  clear IHtyp1 ; clear IHtyp2.

  
  
  rewrite H4 in H0.
  pose (typ_sort H0).
  intuition.
Qed.
*)
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
Lemma conv_sum_abs : forall U V M N, ~ conv (Sum U V) (Abs M N).
Admitted.


Lemma conv_sort_abs : forall s T M, ~ conv (Abs T M) (Srt s).
Admitted.
(*
Lemma sort_conv_eq' : forall G T s, G |- T : Srt s -> forall s', conv T (Srt s') -> T = Srt s'.
Proof.
  intros.
  destruct (church_rosser _ _ H0).
  pose (red_sort_eq H2).
  rewrite e in H1.
  pose (type_sorted H).
  destruct o.
  inversion H3.
  rewrite H5 in H.
  apply sort_conv_eq with G ; auto.
  destruct H3.
  destruct (typ_sort H3).

  generalize H1 ; generalize H ; generalize H0.
  generalize H4 ; generalize s.
  clear H H0 H1 H2 e H3 H4 H5 s.
  generalize s' ; generalize G.
  clear G s' x x0.
  
  induction T ; intros ;  try (simpl in i ; destruct i ; inversion H1 ; try discriminate) ; auto with coc core.

  rewrite (conv_sort _ _ H0).
  auto.

  elim conv_sort_ref with s' n ; auto with coc.

  elim conv_sort_abs with s' T1 T2 ; auto with coc.

  inversion H1.
  inversion H3.
  
  destruct (inv_subst_sort _ _ _ H7).
  rewrite H6 in H5.
  rewrite <- H5 in H2.
  inversion H2.
  rewrite H10 in H.
  pose (sort_of_app2 H).
  pose (n s').
  elim n0 ; auto.

  Foc
  rewrite (conv_sort _ _ H0).
  auto.

  pose (conv_sort_prod s T1 T2).
  pose (sym_conv _ _ H0).
  contradiction.

  pose (conv_sort_sum s T1 T2).
  pose (sym_conv _ _ H0).
  contradiction.

  pose (conv_sort_sum s T1 T2).
  pose (sym_conv _ _ H0).
  contradiction.
Qed.

*)

Lemma conv_dom : 
  forall e A Ts, e |- A : Ts -> 
  forall B s s', Ts = Srt s -> 
  forall s'', e |- B : Srt s'' -> conv A B -> 
  (s = s'') /\
  (type_dom A = Srt s' -> type_dom B = Srt s')
  /\ (type_range A = Srt s' -> type_range B = Srt s')
  .
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  
  split.
  pose (sort_conv_eq).

  inversion H0.
  rewrite <- H5 in H1.
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

  inversion H1.
  assert (e |- Prod T U : Srt s).
  rewrite <- H8.
  apply type_prod with s1 ; auto.
  pose (inv_conv_prod_sort_l H7 H2 H3).
  destruct s0.
  intuition.
  pose (inv_conv_prod_l _ _ _ _ H3).
  apply coerce_env_hd with x0.
  apply coerce_conv with T T ; auto with coc.

  apply wf_var with s1 ; auto with coc.
  apply (inv_conv_prod_r _ _ _ _ H3).

  elim conv_prod_sum with T U B1 B2 ; auto with coc.

  elim conv_prod_subset with T U B1 B2 ; auto with coc.

  pose (term_type_range_kinded H0 H4).
  rewrite H1 in e0.
  inversion e0.
  rewrite H6 in H2.
  pose (gen_sorting_pi1 H2).
  destruct i ; discriminate.

  pose (term_type_range_kinded H0 H4).
  rewrite H1 in e0.
  inversion e0.
  rewrite H6 in H2.
  pose (gen_sorting_pi2 H2).
  destruct i ; discriminate.

  elim (not_t_let_in H2) with B1 B2 ; auto with coc.

  induction B ; simpl ; intros ; try discriminate.
  
  elim conv_sort_sum with s0 T U ; auto with coc.
  elim conv_sum_ref with T U n ; auto with coc.
  elim conv_sum_abs with T U B1 B2 ; auto with coc.

  split ; intros.
  pose (term_type_range_kinded H H5).
  inversion e0.
  rewrite H7 in H1.
  induction H1 ; intuition ; try discriminate.
  rewrite H9 in H2.
  inversion H2.
  rewrite <- H10 in H3.
  pose (gen_sorting_app H3).
  destruct i ; discriminate.

  pose (term_type_range_kinded H0 H5).
  inversion e0.
  rewrite H7 in H1.
  induction H1 ; intuition ; try discriminate.
  rewrite H9 in H2.
  inversion H2.
  rewrite <- H10 in H3.
  pose (gen_sorting_app H3).
  destruct i ; discriminate.

  elim conv_sum_pair with T U B1 B2 B3 ; auto.

  elim conv_prod_sum with B1 B2 T U ; auto with coc.

  assert (e |- Sum T U : Srt s3).
  apply type_sum with s1 s2 ; auto.
  inversion H2.
  rewrite H7 in H5.
  rewrite H7 in H1.
  destruct (inv_conv_sum_sort H5 H3 H4).
  destruct H6.
  destruct H6.
  destruct H8.
  destruct H9.
  destruct H10.
      
  pose (inv_conv_sum_l _ _ _ _ H4).
  pose (inv_conv_sum_r _ _ _ _ H4).

  split ; intros.
  induction H1 ; induction H11 ; intuition ; try rewrite H12 ; try rewrite H1 ; try rewrite H11 ; try discriminate ;
  try (rewrite H15 in H17 ; discriminate) ; auto.
  rewrite H13 in H.
  pose (term_type_range_kinded H H12) ; discriminate.

  rewrite H13 in H.
  pose (term_type_range_kinded H H12) ; discriminate.
  rewrite H13 in H.
  pose (term_type_range_kinded H H12) ; discriminate.

  pose (term_type_range_kinded H H5) ; discriminate.

  destruct (IHtyp1 B1 x s') ; auto with coc. 
  induction H1 ; induction H11 ; intuition ; try rewrite H12 ; try rewrite H1 ; try rewrite H11 ; try discriminate ;
  try (rewrite H14 in H16 ; discriminate) ; auto.

  
  



  pose (IHtyp2 B2 s s') ; auto with coc.
  destruct (generation_prod2 H2).
  apply typ_conv_env with (B1 :: e) ; auto with coc core.
  destruct H5.

  inversion H1.
  assert (e |- Prod T U : Srt s).
  rewrite <- H8.
  apply type_prod with s1 ; auto.
  pose (inv_conv_prod_sort_l H7 H2 H3).
  destruct s0.
  intuition.
  pose (inv_conv_prod_l _ _ _ _ H3).
  apply coerce_env_hd with x0.
  apply coerce_conv with T T ; auto with coc.

  apply wf_var with s1 ; auto with coc.
  apply (inv_conv_prod_r _ _ _ _ H3).


  elim conv_subset_sum with B1 B2 T U ; auto with coc.

  pose (term_type_range_kinded H0 H4).
  rewrite H1 in e0.
  inversion e0.
  rewrite H6 in H2.
  pose (gen_sorting_pi1 H2).
  destruct i ; discriminate.

  pose (term_type_range_kinded H0 H4).
  rewrite H1 in e0.
  inversion e0.
  rewrite H6 in H2.
  pose (gen_sorting_pi2 H2).
  destruct i ; discriminate.

  elim (not_t_let_in H2) with B1 B2 ; auto with coc.



  Focus 2.
  split ; intros ; discriminate.
  Focus 2.
  split ; intros ; discriminate.
  Focus 2.
  split ; intros ; discriminate.
  Focus 2.
  rewrite H3 in H2.
  pose (coerce_propset_r H2).
  apply (IHtyp1 B s0 s' e0 H4 H5).



  destruct (IHtyp2 B2 s s') ; auto with coc.
  destruct (generation_prod2 H2).
  apply typ_conv_env with (B1 :: e) ; auto with coc core.
  destruct H5.

  inversion H1.
  assert (e |- Prod T U : Srt s).
  rewrite <- H8.
  apply type_prod with s1 ; auto.
  pose (inv_conv_prod_sort_l H7 H2 H3).
  destruct s0.
  intuition.
  pose (inv_conv_prod_l _ _ _ _ H3).
  apply coerce_env_hd with x0.
  apply coerce_conv with T T ; auto with coc.

  apply wf_var with s1 ; auto with coc.
  apply (inv_conv_prod_r _ _ _ _ H3).


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

