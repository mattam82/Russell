Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import Conv_Dec.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Substitution.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Lemma lift_rec_eq_sort : forall t n k s, lift_rec n t k = Srt s -> t = Srt s.
Proof.
induction t ; simpl ; intros ; auto with coc core ; try discriminate.

generalize H ; clear H ; elim (le_gt_dec k n) ; intros ; discriminate.
Qed.

Lemma lift_eq_sort : forall t n s, lift n t = Srt s -> t = Srt s.
Proof.
unfold lift ; intros ; apply lift_rec_eq_sort with n 0 ; auto.
Qed.

Lemma typ_not_kind : forall G t T, G |- t : T -> t <> Srt kind.
Proof.
red ; intros.
rewrite H0 in H.
pose (typ_sort _ _ _ H).
induction a.
unfold is_prop in H1.
induction H1 ; discriminate.
Qed.

Lemma typ_not_kind2 : forall G T, ~ G |- Srt kind : T.
Proof.
  unfold not ; intros.
  apply (typ_not_kind H).
  auto.
Qed.

Hint Resolve lift_eq_sort typ_not_kind2 : coc.


Fixpoint type_range (t : term) : term :=
  match t with
  | Prod U V => type_range V
  | Sum U V => type_range V
  | _ => t
  end.

Definition type_dom (t : term) : term :=
  match t with
  | Prod U V => type_range U
  | Sum U V => type_range U
  | _ => type_range t
  end.

Fixpoint type_no_kind (t : term) : Prop :=
  match t with
  | Prod U V => type_no_kind U /\ type_no_kind V
  | Sum U V => type_no_kind U /\ type_no_kind V
  | Srt kind => False
  | _ => True
  end.

Lemma type_has_no_kind : forall G t T, G |- t : T -> type_no_kind t.
Proof.
  induction 1; simpl ; intros ; auto with coc ; try discriminate.
Qed.

Lemma type_no_kind_not_kind : forall t, type_no_kind t -> t <> Srt kind.
Proof.
  induction t ; unfold not ; intros ; try discriminate.
  simpl in H.
  inversion H0.
  rewrite H2 in H.
  auto.
Qed.
(*
Lemma type_range_not_kind_ps : forall G t T, G |- t : T -> 
  forall U V, t = Prod U V \/ t = Sum U V -> type_range U <> Srt kind /\
  type_range V <> Srt kind.
Proof.
  induction 1; simpl ; intros ; auto with coc ; try (intuition ; discriminate).
  destruct H1.

  inversion H1.
  rewrite <- H3.
  rewrite <- H4.
  split.
  apply (type_range_not_kind H).
  apply (type_range_not_kind H0).
  discriminate.

  inversion H1.
  discriminate.
  inversion H2.
  rewrite <- H4.
  rewrite <- H5.
  split.
  apply (type_range_not_kind H).
  apply (type_range_not_kind H0).
Qed.
*)
Lemma lift_type_range_eq_sort : forall n t k, type_no_kind (lift_rec n t k) -> 
  type_no_kind t.
Proof.
  induction t ; simpl ; intros ; try discriminate ; auto.

  intuition.
  apply IHt1 with k ; auto.
  apply IHt2 with (S k) ; auto.

  intuition.
  apply IHt1 with k ; auto.
  apply IHt2 with (S k) ; auto.
Qed.

Lemma type_no_kind_lift : forall n t k, type_no_kind t ->
  type_no_kind (lift_rec n t k).
Proof.
  induction t ; simpl ; intros ; try discriminate ; auto.

  elim (le_gt_dec k n0) ; simpl ; intros ; auto.
  intuition.
  intuition.
Qed.

Lemma type_range_subst_not_kind : forall u v n, type_no_kind u ->
  type_no_kind v -> type_no_kind (subst_rec u v n).
Proof.
  induction v ; simpl ; intros ; try discriminate ; auto.

  elim (lt_eq_lt_dec n0 n) ; intros.
  induction a ; simpl ; intros ; unfold not ; intros ; try discriminate ; auto.
  unfold lift ; apply (type_no_kind_lift); auto.
  auto.

  intuition.
  intuition.
Qed.
 
Lemma type_no_kind_type : forall G t T, G |- t : T -> 
  forall U V, (T = Prod U V \/ T = Sum U V) -> type_no_kind T.
Proof.
  induction 1 using typ_mutwf with
  (P := fun G t T => fun H : G |- t : T =>
  forall U V, (T = Prod U V \/ T = Sum U V) -> type_no_kind T)
  (P0 := fun G U V s => fun H : G |- U >> V : s => True (*
    (forall X Y, U = Prod X Y -> prod_sort Y <> Srt kind) /\
    (forall X Y, U = Prod X Y -> prod_sort Y <> Srt kind)*))
  (P1 := fun e => fun H : wf e => 
    forall T n, item_lift T e n -> 
    forall U V, (T = Prod U V \/ T = Sum U V) -> type_no_kind T)
 ; simpl ; intros ; auto with coc ; try discriminate ; 
 try (destruct H ; discriminate) ;  try (destruct H1 ; discriminate).

  apply IHtyp with n U V ; auto.

  destruct H2 ; try discriminate.
  assert (e |- Prod T U : Srt s2).
  apply type_prod with s1 ; auto with coc.
  pose (type_has_no_kind H3) ; auto with coc.

  destruct H1.
  induction Ur ;  try (unfold subst, subst_rec ; simpl ; intros ; discriminate).
  unfold subst in H1.
  generalize H1 ; clear H1.
  unfold subst_rec ; elim (lt_eq_lt_dec 0 n).
  intro a ; case a ; clear a ; intros ; try discriminate.
  rewrite <- e0 ; simpl.
  unfold subst ; simpl.
  rewrite lift0.
  apply (type_has_no_kind H) ; auto with coc.

  intros ; discriminate.
  pose (IHtyp2 V (Prod Ur1 Ur2) (or_introl _ (refl_equal (Prod V (Prod Ur1 Ur2))))).
  simpl in t.
  destruct t.
  destruct H3.
  unfold subst in H1 ; simpl in H1.
  clear IHUr1 IHUr2.

  inversion H1.

  pose (type_has_no_kind H).
  split ; apply type_range_subst_not_kind ; auto.

  induction Ur ;  try (unfold subst, subst_rec ; simpl ; intros ; discriminate).
  unfold subst in H1.
  generalize H1 ; clear H1.
  unfold subst_rec ; elim (lt_eq_lt_dec 0 n).
  intro a ; case a ; clear a ; intros ; try discriminate.
  rewrite <- e0 ; simpl.
  unfold subst ; simpl.
  rewrite lift0.
  apply (type_has_no_kind H) ; auto with coc.

  intros ; discriminate.
  pose (IHtyp2 V (Sum Ur1 Ur2) (or_introl _ (refl_equal (Prod V (Sum Ur1 Ur2))))).
  simpl in t.
  destruct t.
  destruct H3.
  unfold subst in H1 ; simpl in H1.
  clear IHUr1 IHUr2.

  inversion H1.

  pose (type_has_no_kind H).
  split ; apply type_range_subst_not_kind ; auto.

  destruct H3.
  discriminate.
  inversion H3.
  rewrite <- H6.
  rewrite <- H5.
  split ; [apply (type_has_no_kind H) | apply (type_has_no_kind H1)].
  
  pose (IHtyp U V (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0.
  intuition.
  
  assert(type_no_kind (Pi1 t)) ; auto with coc.
  simpl ; auto.
  unfold subst ; apply type_range_subst_not_kind ; auto.
  intuition.
  pose (IHtyp U V (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0 ; intuition.
  pose (IHtyp U V (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0 ; intuition.
    
  induction M ; intuition ; try discriminate.
  generalize H4 ; unfold subst, subst_rec.
  elim (lt_eq_lt_dec 0 n) ; intros a ; try discriminate.
  case a ; clear a ; intros ; try discriminate.
  rewrite lift0. rewrite lift0 in H3.
  rewrite H3 ; rewrite H3 in H.
  pose (type_has_no_kind H) ; auto with coc.
  
  intros ; discriminate.
  pose (type_has_no_kind H2).
  pose (type_has_no_kind H).
  unfold subst ; apply type_range_subst_not_kind ; auto.
  
  unfold subst in H4 ; simpl in H4.
  inversion H4.
  pose (type_has_no_kind H2).
  pose (type_has_no_kind H).
  unfold subst ; apply type_range_subst_not_kind ; auto.

  unfold subst in H4 ; simpl in H4.
  inversion H4.
  pose (type_has_no_kind H2).
  pose (type_has_no_kind H).
  unfold subst ; apply type_range_subst_not_kind ; auto.
  
  destruct H2 ;
  rewrite H2 in H0 ;
  rewrite H2 ; apply (type_has_no_kind H0).

  destruct H.
  elim (inv_nth_nl _ _ _ H1).
  
  assert (wf (T :: e)). 
  apply wf_var with s ; auto with coc.
  destruct (wf_sort_lift _ (T :: e) _ H2 H0).
  apply (type_has_no_kind H3).
Qed.

Lemma type_no_kind_prod_type : forall G t U V, 
  G |- t : Prod U V -> type_no_kind V.
Proof.
  intros.
  pose (type_no_kind_type H (or_introl _ (refl_equal (Prod U V)))).
  simpl in t0.
  intuition.
Qed.

Lemma type_no_kind_prod_type2 : forall G t U V, 
  G |- t : Prod U V -> type_no_kind (Prod U V).
Proof.
  intros.
  pose (type_no_kind_type H (or_introl _ (refl_equal (Prod U V)))).
  simpl in t0.
  intuition.
  simpl ; auto.
Qed.

Lemma type_no_kind_prod_type_sort : forall G t U V, 
  G |- t : Prod U V -> 
  forall s, type_range V = Srt s -> s <> kind.
Admitted.

Lemma type_no_kind_sum_type : forall G t U V, 
  G |- t : Sum U V -> type_no_kind V.
Proof.
  intros.
  pose (type_no_kind_type H (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0.
  intuition.
Qed.

Definition is_low_sort (s : term) := s = Srt set \/ s = Srt prop.

Lemma subst_to_sort : forall t t' s, subst t t' = Srt s -> t <> Srt s ->
  t' = Srt s.
Proof.
  induction t' ; intros ; try discriminate.
  unfold subst, subst_rec in H.
  assumption.

  unfold subst, subst_rec in H.
  generalize H.
  elim (lt_eq_lt_dec 0 n).
  intros a.
  induction a.
  intros ; discriminate.
  intros.
  rewrite lift0 in H1.
  contradiction.

  intros ; discriminate.
Qed.

Lemma kind_is_prod : forall G t T, G |- t : T -> T = Srt kind ->
  is_low_sort (type_range t).
Proof.
  induction 1 ; intros ; try discriminate ; simpl ; auto.
  unfold is_low_sort ; intuition.
  unfold is_low_sort ; intuition.
  induction (wf_sort_lift _ _ _ H H0).
  rewrite H1 in H2.
  elim (typ_not_kind H2) ; auto.
  
  pose (subst_to_sort _ H1 (typ_not_kind H)).

  pose (type_no_kind_type H0 (or_introl _ (refl_equal (Prod V Ur)))).
  simpl in t.
  destruct t.
  rewrite e0 in H3.
  simpl in H3.
  contradiction.

  pose (type_no_kind_type H (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0.
  destruct t0.
  rewrite H0 in H1.
  simpl in H1.
  contradiction.

  pose (type_no_kind_type H (or_intror _ (refl_equal (Sum U V)))).
  simpl in t0.
  destruct t0.
  assert(Pi1 t <> Srt kind) ; try (unfold not ; intros ; discriminate).
  pose (subst_to_sort _ H0 H3).
  rewrite e0 in H2.
  simpl in H2.
  contradiction.

  pose (type_has_no_kind H).
  pose (type_has_no_kind H2).
  unfold subst in H3.
  pose (type_range_subst_not_kind _ _ 0 t0 t1).
  pose (type_no_kind_not_kind t2).
  contradiction.

  rewrite H3 in H0.
  pose (typ_not_kind H0).
  elim n ; auto.
Qed.

Lemma red_sort_eq : forall s t, red (Srt s) t -> t = Srt s.
Proof.
  simple induction 1; intros; auto with coc core arith sets.
  rewrite H1 in H2.
  inversion H2.
Qed.

Lemma sort_conv_eq : forall G T s, G |- T : Srt kind -> conv T (Srt s) -> T = Srt s.
Proof.
  intros.
  destruct (church_rosser _ _ H0).
  pose (red_sort_eq H2).
  rewrite e in H1.

  pose (kind_is_prod H (refl_equal (Srt kind))).
  unfold is_low_sort in i.
  induction T ; try (simpl in i ; destruct i ; inversion H1 ; try discriminate) ; auto with coc core.

  rewrite (conv_sort _ _ H0).
  auto.

  rewrite (conv_sort _ _ H0).
  auto.

  pose (conv_sort_prod s T1 T2).
  pose (sym_conv _ _ H0).
  contradiction.

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

Lemma coerce_prop_sort_l_aux : forall G Ts A s', G |- Ts >> A : s' ->
  Ts = Srt prop ->  s' = kind -> G |- A : Srt kind -> A = Srt prop.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  apply sort_conv_eq with e ; auto.
  rewrite H2 in H1 ; auto with coc.

  apply IHcoerce2 ; auto.
  apply IHcoerce1 ; auto.
  rewrite H2 in H0.
  apply coerce_sort_l with C ; auto.
Qed.

Lemma coerce_set_sort_l_aux : forall G Ts A s', G |- Ts >> A : s' ->
  Ts = Srt set ->  s' = kind -> G |- A : Srt kind -> A = Srt set.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  apply sort_conv_eq with e ; auto.
  rewrite H2 in H1 ; auto with coc.

  apply IHcoerce2 ; auto.
  apply IHcoerce1 ; auto.
  rewrite H2 in H0.
  apply coerce_sort_l with C ; auto.
Qed.


Lemma coerce_prop_sort_r_aux : forall G Ts A s', G |- A >> Ts : s' ->
  Ts = Srt prop ->  s' = kind -> G |- A : Srt kind -> A = Srt prop.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  apply sort_conv_eq with e ; auto.
  rewrite H2 in H1 ; auto with coc.

  apply IHcoerce1 ; auto.
  apply IHcoerce2 ; auto.
  rewrite H2 in H0.
  apply coerce_sort_l with C ; auto.
Qed.

Lemma coerce_set_sort_r_aux : forall G Ts A s', G |- A >> Ts : s' ->
  Ts = Srt set ->  s' = kind -> G |- A : Srt kind -> A = Srt set.
Proof.
  induction 1 ; simpl ; intros ; try discriminate.
  apply sort_conv_eq with e ; auto.
  rewrite H2 in H1 ; auto with coc.

  apply IHcoerce1 ; auto.
  apply IHcoerce2 ; auto.
  rewrite H2 in H0.
  apply coerce_sort_l with C ; auto.
Qed.

Lemma coerce_prop_sort_l : forall G A, G |- Srt prop >> A : kind -> A = Srt prop.
Proof. 
  intros.
  eapply coerce_prop_sort_l_aux with G (Srt prop) kind ; auto.
  apply coerce_sort_r with (Srt prop) ; auto.
Qed.

Lemma coerce_prop_sort_r : forall G A, G |- A >> Srt prop : kind -> A = Srt prop.
Proof. 
  intros.
  eapply coerce_prop_sort_r_aux with G (Srt prop) kind ; auto.
  apply coerce_sort_l with (Srt prop) ; auto.
Qed.

Lemma coerce_set_sort_l : forall G A, G |- Srt set >> A : kind -> A = Srt set.
Proof. 
  intros.
  eapply coerce_set_sort_l_aux with G (Srt set) kind ; auto.
  apply coerce_sort_r with (Srt set) ; auto.
Qed.

Lemma coerce_set_sort_r : forall G A, G |- A >> Srt set : kind -> A = Srt set.
Proof. 
  intros.
  eapply coerce_set_sort_r_aux with G (Srt set) kind ; auto.
  apply coerce_sort_l with (Srt set) ; auto.
Qed.

Lemma coerce_propset_l : forall G A s s', G |- Srt s >> A : s' -> A = Srt s.
Proof.
  intros.
  assert(s' = kind).
  pose (coerce_sort_l _ _ _ _ H).
  pose (typ_sort _ _ _ t).
  intuition.
  inversion H1 ; auto.
  rewrite H0 in H.
  clear H0.
  induction s.
  pose (coerce_sort_l _ _ _  _ H).
  pose (typ_not_kind t).
  elim n ; auto.
  
  eapply coerce_prop_sort_l with G ; auto with coc.
  eapply coerce_set_sort_l with G ; auto with coc.
Qed.

Lemma coerce_propset_r : forall G A s s', G |- A >> Srt s : s' -> A = Srt s.
Proof.
  intros.
  assert(s' = kind).
  pose (coerce_sort_r _ _ _ _ H).
  pose (typ_sort _ _ _ t).
  intuition.
  inversion H1 ; auto.
  rewrite H0 in H.
  clear H0.
  induction s.
  pose (coerce_sort_r _ _ _  _ H).
  pose (typ_not_kind t).
  elim n ; auto.
  
  eapply coerce_prop_sort_r with G ; auto with coc.
  eapply coerce_set_sort_r with G ; auto with coc.
Qed.


Lemma wf_is_sorted : forall e, wf e ->
  forall x n, item _ x e n -> forall s, x = Srt s -> is_prop s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  elim (inv_nth_nl _ _ _ H).
  pose (item_trunc).
  induction (item_trunc _ _ _ _ H0).

  pose (wf_sort).
  pose (wf_var _ _ _ H).
  induction (wf_sort n _ _ H2 w x H0).
  rewrite H1 in H3.
  pose (typ_sort _ _ _ H3).
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
  pose (typ_sort _ _ _ H0).
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
  pose (typ_sort _ _ _ H0).
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
  destruct (typ_sort _ _ _ H0).
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
  induction (typ_sort _ _ _ H1).
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
  induction (typ_sort _ _  _ H0).
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
  exists s2 ; auto.

  destruct (IHtyp1 U0 V0 H3).
  rewrite H4 in H1.
  induction (typ_sort _ _ _ H1).
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
  induction (typ_sort _ _  _ H0).
  inversion H6.
  rewrite H8 in H2.
  pose (coerce_propset_r H2).

  apply (IHtyp1 U0 V0 H3 s0 e0).
Qed.

Lemma generation_sum2 : forall e U V s, e |- Sum U V : Srt s ->
  (exists s', e |- U : Srt s') /\ (U :: e) |- V : Srt s.
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

Lemma conv_is_low_range : forall A s, conv (Srt s) A -> is_low_sort (type_range A) -> A = Srt s.
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

  elim conv_sort_prod with s A1 A2 ; auto with coc core.
  elim conv_sort_prod with s A1 A2 ; auto with coc core.

  simpl in H0.
  rewrite H0 ; rewrite H2 ; auto.
  
  simpl in H0.
  pose (IHA1 B1 (inv_conv_prod_l _ _ _ _ H)).
  unfold is_low_sort ; rewrite H2 ; auto.
  unfold is_low_sort ; rewrite H0 ; auto.

  simpl in H0.
  apply (IHA1 B1 (inv_conv_prod_l _ _ _ _ H)).
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

Lemma term_type_range_kinded : forall e t T, e |- t : T ->
  forall s, type_range t = Srt s -> T = Srt kind. 
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  
  apply IHtyp2 with s ; auto.
  apply IHtyp2 with s ; auto.
  
  rewrite (IHtyp1 _ H3) in H1.
  elim typ_not_kind2 with e (Srt s) ; auto.
Qed.

Lemma type_range_sub : forall e T U s, e |- T >> U : s ->
  forall s0, type_range U = Srt s0 -> type_range T = Srt s0.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
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
  pose (term_type_range_kinded H0 H2).
  inversion e0.
  rewrite H4 in H0.
  
  apply (conv_is_low_range_full H1).
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

Lemma type_dom_sub : forall e T U s, e |- T >> U : s ->
  forall s0, type_dom U = Srt s0 -> type_dom T = Srt s0.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
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
  
  
  apply (conv_is_low_range_full H1).
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

Lemma var_sort_dom_item : forall e n T, e |- Ref n : T ->
  forall s, type_dom T = (Srt s) -> 
  exists T', item_lift T' e n /\ type_dom T' = Srt s.
Admitted.

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
  inversion H3.
  rewrite <- H7 ; rewrite <- H8.
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
  exists U, exists V, e |- u : Sum U V /\ type_range U = (Srt s).
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  exists U ; exists V.
  inversion H0.
  rewrite <- H3.
  intuition.
  
  apply IHtyp1 ; auto.
  apply (type_range_sub H2 H4).
Qed.

Lemma sort_of_pi1_range :  forall e t Ts, e |- Pi1 t : Ts ->
  forall s, type_range Ts = Srt s ->
  exists U, exists V, e |- t : Sum U V /\ type_range U = (Srt s).
Proof.
  intros. 
  apply sort_of_pi1_range_aux with (Pi1 t) Ts  ; auto ; auto.
Qed.

Lemma sort_of_pi2_range_aux : forall e t Ts, e |- t : Ts ->
  forall u, t = Pi2 u ->
  forall s, type_range Ts = Srt s ->
  exists U, exists V, e |- u : Sum U V /\ type_range (subst (Pi1 u) V) = (Srt s).
Proof.
  induction 1 ; simpl ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  exists U ; exists V.
  inversion H0.
  rewrite <- H3.
  intuition.
  
  apply IHtyp1 ; auto.
  apply (type_range_sub H2 H4).
Qed.

Lemma sort_of_pi2_range :  forall e t Ts, e |- Pi2 t : Ts ->
  forall s, type_range Ts = Srt s ->
  exists U, exists V, e |- t : Sum U V /\ type_range (subst (Pi1 t) V) = (Srt s).
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

  exists U ; exists M.
  inversion H3.
  rewrite <- H6 ; rewrite <- H7.
  intuition.
  
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

Lemma unique_range_sort : forall t e T T', e |- t : T -> e |- t : T' -> 
forall s1 s2, 
(type_range T = Srt s1 -> type_range T' = Srt s2 -> s1 = s2) /\
(type_dom T = Srt s1 -> type_dom T' = Srt s2 -> s1 = s2).
Proof.
  induction t ; simpl ; split ; intros ;
  auto with coc core arith datatypes ; try discriminate.

  destruct (typ_sort _ _ _ H).
  destruct (typ_sort _ _ _ H0).
  rewrite H4 in H1.
  rewrite H6 in H2.
  simpl in H1, H2.
  inversion H2 ; inversion H1.
  auto.

  destruct (typ_sort _ _ _ H).
  destruct (typ_sort _ _ _ H0).
  rewrite H4 in H1.
  rewrite H6 in H2.
  simpl in H1, H2.
  inversion H2 ; inversion H1.
  auto.

  (* Var *)
  exact (unique_var_range_sort H H1 H0 H2).
  exact (unique_var_dom_sort H H1 H0 H2).
    
  (* Abs *)
  induction (sort_of_abs_range H H1).
  do 2 destruct H3 ; intuition.
  induction (sort_of_abs_range H0 H2).
  do 2 destruct H6 ; intuition.

  destruct (IHt2 _ _ _ H3 H6 s1 s2) ; simpl ; auto.


  destruct (IHt2 _ _ _ H3 H6 s1 s2) ; simpl ; auto.


  (* App goes well *)
  induction (sort_of_app_range H H1).
  destruct H3 ; intuition.
  induction (sort_of_app_range H0 H2).
  destruct H6 ; intuition.

  apply (IHt1 _ _ _ H3 H6) ; simpl ; auto.

  pose (term_type_range_kinded H4 H8).
  rewrite e0 in H3.
  pose (type_no_kind_prod_type2 H3).
  simpl in t.
  intuition.

  induction (sort_of_app_range H0 H2).
  destruct H6 ; intuition.

  apply (IHt1 _ _ _ H3 H6) ; simpl ; auto.

  pose (term_type_range_kinded H4 H5).
  rewrite e0 in H3.
  pose (type_no_kind_prod_type2 H3).
  simpl in t.
  intuition.

  pose (term_type_range_kinded H4 H5).
  rewrite e0 in H3.
  pose (type_no_kind_prod_type2 H3).
  simpl in t.
  intuition.

  (* Pair *)
  induction (sort_of_pair_range H H1).
  do 3 destruct H3 ; intuition.
  induction (sort_of_pair_range H0 H2).
  do 3 destruct H9 ; intuition.

  apply (IHt3 _ _ _ H7 H14) ; simpl ; auto.
  unfold subst ; apply type_range_subst2 ; auto.
  unfold subst ; apply type_range_subst2 ; auto.
  
  (* Prod *)
  induction (generation_prod H).
  induction (generation_prod H0).
  rewrite H3 in H.
  rewrite H4 in H0.
  induction (generation_prod2 H).
  induction (generation_prod2 H0).
  apply (IHt2 _ _ _ H6 H8).
  rewrite <- H3 ; auto.
  rewrite <- H4 ; auto.

  (* Sum *)
  induction (generation_sum H).
  induction (generation_sum H0).
  rewrite H3 in H.
  rewrite H4 in H0.
  induction (generation_sum2 H).
  induction (generation_sum2 H0).
  apply (IHt2 _ _ _ H6 H8).
  rewrite <- H3 ; auto.
  rewrite <- H4 ; auto.
  
  pose (generation_subset H).
  pose (generation_subset H0).
  rewrite e0 in H1.
  rewrite e1 in H2.
  simpl in H1 ; simpl in H2.
  rewrite H2 in H1.
  inversion H1 ; auto.

  (* Pi1 *)
  induction (sort_of_pi1_range H H1).
  destruct H3 ; intuition.
  induction (sort_of_pi1_range H0 H2).
  destruct H3 ; intuition.

  apply (IHt _ _ _ H4 H6) ; simpl ; auto.

  pose (term_type_range_kinded H4 H8).
  rewrite e0 in H3.
  pose (type_no_kind_prod_type2 H3).
  simpl in t.
  intuition.

  induction (sort_of_app_range H0 H2).
  destruct H6 ; intuition.

  apply (IHt1 _ _ _ H3 H6) ; simpl ; auto.

  pose (term_type_range_kinded H4 H5).
  rewrite e0 in H3.
  pose (type_no_kind_prod_type2 H3).
  simpl in t.
  intuition.

  pose (term_type_range_kinded H4 H5).
  rewrite e0 in H3.
  pose (type_no_kind_prod_type2 H3).
  simpl in t.
  intuition.



Admitted. 
(* Focus 3.

  split.
  intros.
  apply trans_conv_conv with A ; auto with coc core.

  intros.
  apply trans_conv_conv with B ; auto with coc core.
*)

Theorem unique_sort : forall t e s s', 
  e |- t : (Srt s) -> e |- t : (Srt s') -> s = s'.
Proof.
  intros.
  exact (unique_range_sort H H0 (refl_equal (Srt s)) (refl_equal (Srt s'))).
Qed.
  
  


