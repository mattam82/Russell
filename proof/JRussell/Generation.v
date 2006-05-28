Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Conv_Dec.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.JRussell.Types.
Require Import Lambda.JRussell.Basic.
Require Import Lambda.JRussell.Conversion.
Require Import Lambda.JRussell.Coercion.
Require Import Lambda.JRussell.Thinning.
Require Import Lambda.JRussell.Substitution.
Require Import Lambda.JRussell.PreFunctionality.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Lemma inv_lift_sort : forall t s n, lift n t = Srt s -> t = Srt s.
Proof.
intros.
induction t ; simpl ; try discriminate.
unfold lift in H ; simpl in H.
auto.
Qed.

Lemma inv_subst_sort : forall t t' n s, subst_rec t t' n = Srt s -> 
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

Ltac extensionalpattern a :=
let t := fresh "t" in (
let H := fresh "H" in (
let Heqt := fresh "Heqt" in (
set (t := a) ; intro H ;
assert(Heqt : t = a) ; [ (unfold t ; reflexivity) |
generalize H Heqt ; clear H Heqt ;
generalize t ; clear t ; intros t]))).

Lemma jeq_not_kind : forall e T U W, e |-= T = U : W -> (T = Srt kind -> False) /\ (U = Srt kind -> False).
Proof.
  induction 1 ; simpl ; intros ; split ; intros ; 
  (try destruct IHjeq) ; (try destruct IHjeq1) ; (try destruct IHjeq2) ;
  try discriminate ; auto with coc.
  
  apply H2 ; apply (inv_lift_sort _ _ H1).
  apply H3 ; apply (inv_lift_sort _ _ H1).

  destruct (inv_subst_sort _ _ _ H3).
  rewrite H4 in H2.
  elim (left_not_kind H2) ; auto.
  elim (left_not_kind H1) ; auto.

  elim (left_not_kind H2) ; auto.
  elim (left_not_kind H3) ; auto.
  
  elim (left_not_kind H) ; auto.
  elim (left_not_kind H) ; auto.
Qed.

Lemma coerce_not_kind : forall e T U s, e |-= T >> U : s -> (T = Srt kind -> False) /\ (U = Srt kind -> False).
Proof.
  induction 1 ; simpl ; intros ; split ; intros ; 
  (try destruct IHcoerce) ; (try destruct IHcoerce1) ; (try destruct IHcoerce2) ;
  try discriminate ; auto with coc.
  
  elim (jeq_not_kind H) ; auto.
  elim (jeq_not_kind H) ; auto.
  
  apply H2 ; apply (inv_lift_sort _ _ H1).
  apply H3 ; apply (inv_lift_sort _ _ H1).
Qed.

Inductive equiv : env -> term -> term -> Prop :=
 |equiv_refl : forall e T, equiv e T T
 |equiv_step : forall e T U s, e |-= T >> U : s -> forall V, equiv e U V -> equiv e T V.

Lemma equiv_lift : forall e T U, equiv e T U -> 
 forall V s, e |-= V : Srt s -> equiv (V :: e) (lift 1 T) (lift 1 U).
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  left ; auto.
  
  right with (lift 1 U) s.
  apply coerce_weak with s0 ; auto.
  apply IHequiv with s0 ; auto with coc.
Qed.

Hint Resolve equiv_refl : coc.

Lemma equiv_coerce : forall e V V', equiv e V V' -> forall T U,
  forall s, e |-= T >> U : s ->
  forall s', e |-= T >> V : s' -> equiv e U V'.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.

  right with T0 s ; auto with coc.
  right with T s' ; auto with coc.

  right with T0 s0 ; auto with coc.
  right with T s' ; auto with coc.
  right with U s ; auto with coc.
Qed.

Lemma equiv_kind : forall e U, equiv e U (Srt kind) -> U = Srt kind.
Proof.
  intros e U.
  extensionalpattern (Srt kind).
  induction 1 ; simpl ; intros ; auto with coc.
  
  destruct H0.
  pose (coerce_not_kind H).
  intuition.

  pose (IHequiv Heqt).
  rewrite Heqt in e0.
  elim (coerce_not_kind H).
  intuition.
Qed.

Lemma generation_sort :  forall e s T, e |-= Srt s : T -> equiv e T (Srt kind).
Proof.
  intros e s T.
  extensionalpattern (Srt s).
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  pose (inv_lift_sort _ _ Heqt).
  pose (IHtyp1 e0).
  pose (equiv_kind e1).
  rewrite e2.
  simpl ; left ; auto with coc.

  pose (IHtyp Heqt).
  pose (equiv_kind e0).
  rewrite e1 in H0.
  elim (coerce_not_kind H0) ; intros.
  elim H1 ; auto.
Qed.

Lemma inv_lift_ref : forall t n, lift 1 t = Ref n -> exists n', t = Ref n' /\ S n' = n.
Proof.
  induction t ; simpl ; intros ; try discriminate ; auto with coc.
  unfold lift in H ; simpl in H.
  inversion H.
  exists n ; intuition.
Qed.

Lemma generation_var_aux : forall e T A, e |-= T : A -> 
  forall n, T = Ref n ->
  exists B, item_lift B e n /\ equiv e A B.
Proof.
  intros e T A.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  inversion H0.
  exists (lift 1 T).
  split.
  exists T ; auto.
  constructor.
  left ; auto with coc.
  
  pose (inv_lift_ref _ H1).
  destruct e0.
  destruct H2.
  destruct (IHtyp1 _ H2).
  destruct H4.
  exists (lift 1 x0).
  split.
  destruct H4.
  exists x1 ; auto.
  rewrite H4.
  rewrite <- simpl_lift.
  rewrite H3.
  reflexivity.
  rewrite <- H3.
  constructor.
  assumption.

  apply equiv_lift with s ; auto.

  pose (IHtyp _ H1).
  destruct e0.
  destruct H2.
  exists x ; intuition.
  right with U s ; auto with coc.
Qed.

Lemma generation_var : forall e n A, e |-= Ref n : A -> 
  exists B, item_lift B e n /\ equiv e A B.
Proof.
  intros ; eapply generation_var_aux ; auto ; auto.
Qed.

Lemma generation_prod_aux : forall e T A, e |-= T : A -> forall U V, T = Prod U V ->
  exists s1, exists s2, e |-= U : Srt s1 /\ U :: e |-= V : Srt s2 /\ equiv e A (Srt s2).
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  induction t ; simpl in H1 ; try discriminate.
  clear IHt1 IHt2.
  destruct (IHtyp1 t1 t2) ; auto with coc.
  destruct H2.
  intuition.
  unfold lift in H1 ; simpl in H1.
  inversion H1.
  exists x ; exists x0.
  intuition ; auto with coc.
  change (Srt x) with (lift 1 (Srt x)).
  unfold lift.
  pose (type_weak H3 H0) ; auto with coc.

  

  change (Srt x0) with (lift_rec 1 (Srt x0) 1).
  apply (type_weak_weak H0 H2) ; auto with coc.
  
  pose (equiv_lift H5 H0).
  unfold lift in e0 ; simpl in e0.
  unfold lift ; apply e0.

  inversion H1.
  rewrite <- H3 ; rewrite <- H4.
  exists s1 ; exists s2 ; intuition ; auto with coc.
  
  destruct (IHtyp _ _ H1).
  destruct H2.
  intuition.
  exists x ; exists x0 ; intuition ; auto with coc.
  right with U s ; auto with coc.
Qed.

Lemma generation_prod : forall e U V A, e |-= Prod U V : A -> 
  exists s1, exists s2, e |-= U : Srt s1 /\ U :: e |-= V : Srt s2 /\ equiv e A (Srt s2).
Proof.
  intros ; eapply generation_prod_aux ; auto ; auto.
Qed.

Lemma generation_sum_aux : forall e T A, e |-= T : A -> forall U V, T = Sum U V ->
  exists s1, exists s2, exists s3,
  e |-= U : Srt s1 /\ 
  U :: e |-= V : Srt s2 /\
  sum_sort s1 s2 s3 /\
  equiv e A (Srt s3).
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  destruct t ; simpl in H1 ; try discriminate.
  destruct (IHtyp1 t1 t2) ; auto with coc.
  destruct H2.
  destruct H2.
  intuition.
  unfold lift in H1 ; simpl in H1.
  inversion H1.
  exists x ; exists x0 ; exists x1.
  intuition ; auto with coc.
  change (Srt x) with (lift 1 (Srt x)).
  unfold lift.
  pose (type_weak H3 H0) ; auto with coc.
  change (Srt x0) with (lift_rec 1 (Srt x0) 1).
  apply (type_weak_weak H0 H2) ; auto with coc.
  
  pose (equiv_lift H6 H0).
  unfold lift in e0 ; simpl in e0.
  unfold lift ; apply e0.

  inversion H2.
  rewrite <- H4 ; rewrite <- H5.
  exists s1 ; exists s2 ; exists s3 ; intuition ; auto with coc.
  
  destruct (IHtyp _ _ H1).
  do 2 destruct H2.
  intuition.
  exists x ; exists x0 ; exists x1 ; intuition ; auto with coc.
  right with U s ; auto with coc.
Qed.

Lemma generation_sum : forall e U V A, e |-= Sum U V : A -> 
  exists s1, exists s2, exists s3,
  e |-= U : Srt s1 /\ 
  U :: e |-= V : Srt s2 /\
  sum_sort s1 s2 s3 /\
  equiv e A (Srt s3).
Proof.
  intros ; eapply generation_sum_aux ; auto ; auto.
Qed.

Lemma generation_lambda_aux : forall e t A, e |-= t : A -> forall T M, t = Abs T M ->
  exists s1, exists s2, exists C, 
  e |-= T : Srt s1 /\ 
  T :: e |-= C : Srt s2 /\
  T :: e |-= M : C /\
  equiv e A (Prod T C).
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  destruct t ; simpl in H1 ; try discriminate.
  destruct (IHtyp1 t1 t2) ; auto with coc.
  do 2 destruct H2.
  intuition.
  unfold lift in H1 ; simpl in H1.
  inversion H1.
  exists x ; exists x0 ; exists (lift_rec 1 x1 1).
  intuition ; auto with coc.
  change (Srt x) with (lift 1 (Srt x)).
  unfold lift.
  pose (type_weak H3 H0) ; auto with coc.

  change (Srt x0) with (lift_rec 1 (Srt x0) 1).
  apply (type_weak_weak H0 H2) ; auto with coc.

  apply (type_weak_weak H0 H4) ; auto with coc.
  
  pose (equiv_lift H6 H0).
  apply e0.

  inversion H2.
  rewrite <- H4 ; rewrite <- H5.
  exists s1 ; exists s2 ; exists U ; intuition ; auto with coc.
  
  destruct (IHtyp _ _ H1).
  do 2 destruct H2.
  intuition.
  exists x ; exists x0 ; exists x1 ; intuition ; auto with coc.
  right with U s ; auto with coc.
Qed.

Lemma generation_lambda : forall e T M A, e |-= Abs T M : A -> 
  exists s1, exists s2, exists C, 
  e |-= T : Srt s1 /\ 
  T :: e |-= C : Srt s2 /\
  T :: e |-= M : C /\
  equiv e A (Prod T C).
Proof.
  intros ; eapply generation_lambda_aux ; auto ; auto.
Qed.

Lemma generation_app_aux : forall e t C, e |-= t : C -> forall M N, t = App M N ->
  exists A, exists B,
  e |-= M : Prod A B /\ 
  e |-= N : A /\
  equiv e C (subst N B).
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  destruct t ; simpl in H1 ; try discriminate.
  destruct (IHtyp1 t1 t2) ; auto with coc.
  do 2 destruct H2.
  intuition.
  unfold lift in H1 ; simpl in H1.
  inversion H1.
  exists (lift_rec 1 x 0) ; exists (lift_rec 1 x0 1); intuition ; auto with coc.
  pose (type_weak H2 H0) ; auto with coc.

  apply (type_weak_lift_rec H4 H0) ; auto with coc.
  
  pose (equiv_lift H5 H0).
  rewrite <- distr_lift_subst.
  apply e0.

  inversion H1.
  rewrite <- H4 ; rewrite <- H3.
  exists V ; exists Ur ; intuition ; auto with coc.
  
  destruct (IHtyp _ _ H1).
  do 2 destruct H2.
  intuition.
  exists x ; exists x0 ; intuition ; auto with coc.
  right with U s ; auto with coc.
Qed.

Lemma generation_app : forall e M N C, e |-= App M N : C -> 
  exists A, exists B,
  e |-= M : Prod A B /\ 
  e |-= N : A /\
  equiv e C (subst N B).
Proof.
  intros ; eapply generation_app_aux ; auto ; auto.
Qed.

Lemma generation_pair_aux : forall e t C, e |-= t : C -> forall T M N, t = Pair T M N ->
  exists A, exists B, exists s1, exists s2, exists s3,
  T = Sum A B /\
  e |-= A : Srt s1 /\
  A :: e |-= B : Srt s2 /\
  sum_sort s1 s2 s3 /\
  e |-= M : A /\ 
  e |-= N : subst M B /\
  equiv e C (Sum A B).
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  destruct t ; simpl in H1 ; try discriminate.
  destruct (IHtyp1 t1 t2 t3) ; auto with coc.
  do 4 destruct H2.
  intuition.
  unfold lift in H1 ; simpl in H1.
  inversion H1.
  exists (lift_rec 1 x 0) ; exists (lift_rec 1 x0 1);
  exists x1 ; exists x2 ; exists x3 ; intuition ; auto with coc.
  clear IHtyp2.
  rewrite H3 ; simpl ; auto.
  
  change (Srt x1) with (lift_rec 1 (Srt x1) 0).
  apply (type_weak H2 H0) ; auto with coc.

  change (Srt x2) with (lift_rec 1 (Srt x2) 1).
  apply (type_weak_weak H0 H4) ; auto with coc.

  pose (type_weak H6 H0) ; auto with coc.

  rewrite <- distr_lift_subst.
  apply (type_weak_lift_rec H7 H0) ; auto with coc.
  
  pose (equiv_lift H9 H0).
  apply e0.

  inversion H4.
  rewrite <- H7 ; rewrite <- H8.
  exists U ; exists V ; exists s1 ; exists s2 ; exists s3 ; intuition ; auto with coc.
   
  destruct (IHtyp _ _ _ H1).
  do 4 destruct H2.
  intuition.
  exists x ; exists x0 ; exists x1 ; exists x2 ; exists x3 ; intuition ; auto with coc.
  right with U s ; auto with coc.
Qed.

Lemma generation_pair : forall e T M N C, e |-= Pair T M N : C ->
  exists A, exists B, exists s1, exists s2, exists s3,
  T = Sum A B /\
  e |-= A : Srt s1 /\
  A :: e |-= B : Srt s2 /\
  sum_sort s1 s2 s3 /\
  e |-= M : A /\ 
  e |-= N : subst M B /\
  equiv e C (Sum A B).
Proof.
  intros ; eapply generation_pair_aux ; auto ; auto.
Qed.

Lemma generation_pi1_aux : forall e t C, e |-= t : C -> forall M, t = Pi1 M ->
  exists A, exists B,
  e |-= M : Sum A B /\ 
  equiv e C A.
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  destruct t ; simpl in H1 ; try discriminate.
  destruct (IHtyp1 t) ; auto with coc.
  destruct H2.
  intuition.
  unfold lift in H1 ; simpl in H1.
  inversion H1.
  exists (lift_rec 1 x 0) ; exists (lift_rec 1 x0 1); intuition ; auto with coc.
  pose (type_weak H3 H0) ; auto with coc.

  pose (equiv_lift H4 H0).
  apply e0.

  inversion H0.
  rewrite <- H2.
  exists U ; exists V ; intuition ; auto with coc.
  
  destruct (IHtyp _ H1).
  destruct H2.
  intuition.
  exists x ; exists x0 ; intuition ; auto with coc.
  right with U s ; auto with coc.
Qed.

Lemma generation_pi1 : forall e M C, e |-= Pi1 M : C ->
  exists A, exists B,
  e |-= M : Sum A B /\ 
  equiv e C A.
Proof.
  intros ; eapply generation_pi1_aux ; auto ; auto.
Qed.

Lemma generation_pi2_aux : forall e t C, e |-= t : C -> forall M, t = Pi2 M ->
  exists A, exists B,
  e |-= M : Sum A B /\ 
  equiv e C (subst (Pi1 M) B).
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.

  destruct t ; simpl in H1 ; try discriminate.
  destruct (IHtyp1 t) ; auto with coc.
  destruct H2.
  intuition.
  unfold lift in H1 ; simpl in H1.
  inversion H1.
  exists (lift_rec 1 x 0) ; exists (lift_rec 1 x0 1); intuition ; auto with coc.
  pose (type_weak H3 H0) ; auto with coc.

  pose (equiv_lift H4 H0).
  unfold lift in e0.
  rewrite distr_lift_subst in e0.
  simpl in e0.
  apply e0.

  inversion H0.
  rewrite <- H2.
  exists U ; exists V ; intuition ; auto with coc.
  
  destruct (IHtyp _ H1).
  destruct H2.
  intuition.
  exists x ; exists x0 ; intuition ; auto with coc.
  right with U s ; auto with coc.
Qed.

Lemma generation_pi2 : forall e M C, e |-= Pi2 M : C ->
  exists A, exists B,
  e |-= M : Sum A B /\ 
  equiv e C (subst (Pi1 M) B).
Proof.
  intros ; eapply generation_pi2_aux ; auto ; auto.
Qed.

