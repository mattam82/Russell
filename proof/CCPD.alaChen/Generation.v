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

Fixpoint prod_sort (t : term) : term :=
  match t with
  | Prod U V => prod_sort V
  | _ => t
  end.

Inductive prod_target : term -> nat -> term -> Prop :=
| prod_target_S : forall U V T n, prod_target V n T -> prod_target (Prod U V) (S n) (lift 1 T)
| prod_target_0 : forall T, forall U V, T <> Prod U V -> prod_target T 0 T.

Definition prod_dec : forall t, {exists U, exists V, t = Prod U V} + {forall U V, t <> Prod U V}.
Proof.
intros.
induction t ; try solve [right ; intros ; red ; intros ; discriminate].
left.
exists t1 ; exists t2 ; reflexivity.
Qed.

Lemma inv_lift_sort : forall t s n, lift n t = Srt s -> t = Srt s.
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
auto.
Qed.

Lemma inv_lift_prod : forall t U V n, lift n t = Prod U V ->
 exists U', exists V', t = Prod U' V' /\ U = (lift_rec n U' 0) /\ V = (lift_rec n V' 1).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t1 ; exists t2 ; split ; [auto | split ; auto].
Qed.

Lemma inv_lift_sum : forall t U V n, lift n t = Sum U V ->
 exists U', exists V', t = Sum U' V' /\ U = (lift_rec n U' 0) /\ V = (lift_rec n V' 1).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t1 ; exists t2 ; split ; [auto | split ; auto].
Qed.

Lemma inv_lift_subset : forall t U V n, lift n t = Subset U V ->
 exists U', exists V', t = Subset U' V' /\ U = (lift_rec n U' 0) /\ V = (lift_rec n V' 1).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t1 ; exists t2 ; split ; [auto | split ; auto].
Qed.

Lemma inv_lift_abs : forall t U V n, lift n t = Abs U V ->
 exists U', exists V', t = Abs U' V' /\ U = (lift_rec n U' 0) /\ V = (lift_rec n V' 1).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t1 ; exists t2 ; split ; [auto | split ; auto].
Qed.

Lemma inv_lift_app : forall t U V n, lift n t = App U V ->
 exists U', exists V', t = App U' V' /\ U = (lift_rec n U' 0) /\ V = (lift_rec n V' 0).
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
injection H ; intros.
exists t1 ; exists t2 ; split ; [auto | split ; auto].
Qed.
(*
Lemma prod_no_kind : forall t G T, G |- t : T -> 
  forall U V, t = Prod U V -> ~ (exists n, prod_target t n (Srt kind)).*)

(*Ltac doubleind t := induction t as [dH1] ; induction dH1 as [dH2].*)

Lemma prod_target_not_kind : forall t G T, G |- t : T -> 
  forall U V, t = Prod U V -> ~ (exists n, prod_target t n (Srt kind)).
Proof.
induction t ; try solve [unfold prod_sort ; red ; intros ; try discriminate].
intros.
induction (prod_dec V).
induction a.
induction H1.
red ; intros.
rewrite H0 in H2.
simpl in H2.
injection H0.
intros.
rewrite H3 in IHt2.

induction H ; try discriminate.

injection H0 ; intros.
rewrite H7 in H5.
rewrite H6 in H5.
apply (IHt2 _ _ H5 _ _ H1).
induction H2.
inversion H2.
pose (inv_lift_sort T0 1 H12).
rewrite e0 in H11.
exists n ; rewrite H12 ; apply H11.

apply (IHtyp1 H0).

injection H0 ; intros.
rewrite H1 in IHt2.
induction H ; try discriminate.
injection H0 ; intros.
rewrite H4 in H3.

red ; intros.

simpl in H6.
rewrite H4 in H6.
induction H6.
inversion H6.
pose (inv_lift_sort T0 1 H11).
induction V ; try solve [
  inversion H10 ; rewrite H15 in H3 ; rewrite e0 in H3 ; apply (typ_not_kind H3) ; auto ].
clear IHV1 ; clear IHV2.

apply (b V1 V2) ; auto.

apply IHtyp1 ; auto.
Qed.
(* 
Lemma typ_sort : forall G t T, G |- t : T -> T <> Srt kind -> 
  exists s, G |- T : Srt s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.

  elim H0 ; auto.

  elim H0 ; auto.
  
  exact (wf_sort_lift n e T H H0).
  
  destruct (IHtyp3 (typ_not_kind H0)).
  exists x.
  apply type_prod with s1 ; auto with coc core.

  assert(Prod V Ur <> Srt kind) ; unfold not ; intros ; try discriminate.
  destruct (IHtyp2 H2).
  exists x.
*)

Lemma prod_arity_not_kind : forall G t T, G |- t : T -> 
  prod_sort t <> Srt kind.
Proof.
  induction 1; simpl ; intros ; auto with coc ; try discriminate.
Qed.

Lemma prod_lift_to_sort : forall n t k s, prod_sort (lift_rec n t k) = Srt s -> prod_sort t = Srt s.
Proof.
  induction t ; simpl ; intros ; try discriminate.
  assumption.
  generalize H ; elim (le_gt_dec k n0) ; intros ; simpl in H0 ; discriminate.
  apply IHt2 with (S k) ; auto.
Qed.

Lemma prod_subst_to_sort : forall u v n, prod_sort u <> Srt kind ->
  prod_sort v <> Srt kind -> prod_sort (subst_rec u v n) <> Srt kind.
Proof.
  induction v ; simpl ; intros ; try discriminate.
  assumption.
  elim (lt_eq_lt_dec n0 n) ; intros.
  induction a ; simpl ; intros ; unfold not ; intros ; try discriminate.
  unfold lift in H1.
  pose (prod_lift_to_sort n0 u 0 H1).
  contradiction.
  simpl ; unfold not ; intros ; discriminate.
  
  apply IHv2 ; auto with coc.
Qed.
 
Lemma prod_arity_not_kind_type : forall G t T, G |- t : T -> 
  forall U V, T = Prod U V -> prod_sort V <> Srt kind.
Proof.
  induction 1 using typ_mutwf with
  (P := fun G t T => fun H : G |- t : T =>
    forall U V, T = Prod U V -> prod_sort V <> Srt kind)
  (P0 := fun G U V s => fun H : G |- U >> V : s => True (*
    (forall X Y, U = Prod X Y -> prod_sort Y <> Srt kind) /\
    (forall X Y, U = Prod X Y -> prod_sort Y <> Srt kind)*))
  (P1 := fun e => fun H : wf e => 
    forall U V n, item_lift (Prod U V) e n -> prod_sort V <> Srt kind) 
 ; simpl ; intros ; auto with coc ; try discriminate.

  apply IHtyp with U n. 
  rewrite H in i ; assumption.

  assert (e |- Prod T U : Srt s2).
  apply type_prod with s1 ; auto with coc.
  rewrite H2 in H3.
  pose (prod_arity_not_kind H3) ; auto with coc.

  induction Ur ;  try (unfold subst, subst_rec ; simpl ; intros ; discriminate).
  unfold subst in H1.
  generalize H1 ; clear H1.
  unfold subst_rec ; elim (lt_eq_lt_dec 0 n).
  intro a ; case a ; clear a ; intros ; try discriminate.
  rewrite lift0 in H1.
  rewrite H1 in H.
  pose (prod_arity_not_kind H) ; auto with coc.

  intros ; discriminate.
  pose (IHtyp2 V (Prod Ur1 Ur2) (refl_equal (Prod V (Prod Ur1 Ur2)))).
  simpl in n.
  unfold subst in H1 ; simpl in H1.
  clear IHUr1 IHUr2.

  inversion H1.

  pose (prod_arity_not_kind H).
  apply prod_subst_to_sort ; auto.

  
  
  Focus 3.
  induction M ; simpl in H3 ; try discriminate.
  generalize H3 ; unfold subst, subst_rec.
  elim (lt_eq_lt_dec 0 n) ; intros a ; try discriminate.
  case a ; clear a ; intros ; try discriminate.
  rewrite lift0 in H4.
  rewrite H4 in H.
  pose (prod_arity_not_kind H) ; auto with coc.
  
  intros ; discriminate.
  pose (prod_arity_not_kind H2).
  simpl in n.
  
  unfold subst in H3 ; simpl in H3.
  inversion H3.
  pose (prod_arity_not_kind H).
  apply prod_subst_to_sort ; auto.

  Focus 3.
  rewrite H2 in H0.
  apply (prod_arity_not_kind H0).

  Focus 3.
  destruct H.
  elim (inv_nth_nl _ _ _ H0).
  
  Focus 3.
  assert (wf (T :: e)). 
  apply wf_var with s ; auto with coc.
  destruct (wf_sort_lift _ (T :: e) _ H1 H0).
  apply (prod_arity_not_kind H2).


Lemma prod_target_not_kindtype : forall t G T, G |- t : T -> 
  forall U V, T = Prod U V -> ~ (exists n, prod_target T n (Srt kind)).
Proof.
induction T ; try solve [unfold prod_sort ; red ; intros ; try discriminate].
intros.
induction (prod_dec V).
induction a.
induction H1.
red ; intros.
rewrite H0 in H2.
simpl in H2.
injection H0.
intros.
rewrite H3 in IHT2.

induction H ; try discriminate.

injection H0 ; intros.
rewrite H6 in H5.
apply (IHT2 _ _ H5 _ _ H1).
induction H2.
inversion H2.
pose (inv_lift_sort T0 1 H12).
rewrite e0 in H11.
exists n ; rewrite H12 ; apply H11.

apply (IHtyp1 H0).

injection H0 ; intros.
rewrite H1 in IHt2.
induction H ; try discriminate.
injection H0 ; intros.
rewrite H4 in H3.

red ; intros.

simpl in H6.
rewrite H4 in H6.
induction H6.
inversion H6.
pose (inv_lift_sort T0 1 H11).
induction V ; try solve [
  inversion H10 ; rewrite H15 in H3 ; rewrite e0 in H3 ; apply (typ_not_kind H3) ; auto ].
clear IHV1 ; clear IHV2.

apply (b V1 V2) ; auto.

apply IHtyp1 ; auto.



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
  is_low_sort (prod_sort t).
Proof.
  induction 1 ; intros ; try discriminate ; simpl ; auto.
  unfold is_low_sort ; intuition.
  unfold is_low_sort ; intuition.
  induction (wf_sort_lift _ _ _ H H0).
  rewrite H1 in H2.
  elim (typ_not_kind H2) ; auto.
  
  pose (subst_to_sort _ H1 (typ_not_kind H)).

  pose (prod_target_not_kind). H0) . (refl_equal (Prod V Ur))).
  


  pose (typ_sort H).

typ_lift_sort).


(*
Lemma prod_target_dec : forall T U, {exists n, prod_target T n U} + {forall n, ~ prod_target T n U}.
Proof.
  intros.
  set (Tfull := T).
  induction T ; 
  (induction (eqterm Tfull U) as [a | a] ; [
  (left ; exists 0 ; rewrite <- a ;
  unfold Tfull ; eapply prod_target_0 ; auto ; red ; intros ; try discriminate) |
  (right ; intros ; red ; intros ; inversion H ; try contradiction) ]).
  

  induction IHT2.
Admitted.

Lemma prod_subst_aux : forall C n a, 
 forall B, prod_target (subst a C) n B -> 
 (exists k, k < n /\ prod_target C k (Ref k) /\ prod_target a (n - k) B) \/
 (exists B', prod_target C n B' /\ subst a B' = B).
Proof.


Lemma typ_prod_not_kind : forall T G t, G |- t : T -> 
  forall U V, T = Prod U V -> ~ (exists n, prod_target T n (Srt kind)).
Proof.
induction T ; try solve [ intros ; discriminate ].
induction 1 ; intros ; try discriminate.
induction (wf_sort_lift _ _ _ H H0).

rewrite H1 in H2.
pose (prod_target_not_kind H2).
simpl in n0.
rewrite H1 ; apply n0 with U V ; auto with coc.

injection H2.
intros.
rewrite H4 in H.
rewrite H3 in H0.
rewrite H4 in H0.
pose (type_prod _ _ _ H _ _ H0).
pose (prod_target_not_kind t).
simpl in n.
rewrite H2 ; apply n with U0 V ; auto.

red ; intros.
induction H2.

rewrite H1 in H2.
inversion H2.
pose (inv_lift_sort T 1 H7).
rewrite e0 in H6.
generalize 
induction n.
inversion H6.
rewrite H11 in H1.
induction Ur ; try solve [unfold subst in H1 ; simpl in H1 ; try discriminate].

unfold subst in H1.
generalize H1.
clear H1.
unfold subst_rec.
elim (lt_eq_lt_dec 0 n) ; intros.
induction a ; try discriminate.
rewrite lift0 in H1.
rewrite H1 in H.
induction (prod_target_not_kind H (refl_equal (Prod U (Srt kind)))).
exists 1.
pattern (Srt kind) at 2.
replace (Srt kind) with (lift 1 (Srt kind)).
apply prod_target_S.
apply prod_target_0 with U1 V2 ; auto.
unfold lift ; simpl ; auto.
discriminate.

unfold subst in H1 ; simpl in H1.

apply H10 ; intros.

pose (IHtyp2 V Ur (refl_equal (Prod V Ur))).


induction (prod_target_dec Ur (Ref 0)).
induction a.


cut (exists n, prod_target (subst v Ur) (n + x0)  

assert(prod_sort (subst v Ur) 

Lemma unicity_sorting : forall G T s1, G |- T : Srt s1 ->
  forall s2, G |- T : Srt s2 -> s1 = s2.
Admitted.
*)
(*
Lemma coerce_trans : forall e T U, 
  e |- T >> U -> 
  forall s,
  e |- T : Srt s ->
  e |- U : Srt s ->
  forall V, e |- V : Srt s ->
  e |- U >> V ->
  e |- T >> V.
Proof.
do 4 intro.
induction H.
intros ; assumption.
intros.

inversion_clear H6.
apply coerce_prod with s ; auto with coc.

pose (unicity_sorting HIHt H8).
rewrite <- e in H7.
pose (IHcoerce1 _ H H0 _ H7).

apply coerce_prod with s ; auto with coc.

*)


















