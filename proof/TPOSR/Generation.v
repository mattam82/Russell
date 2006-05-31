Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Basic.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.CtxConversion.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.Equiv.
Require Import Lambda.TPOSR.TypesDepth.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Lemma generation_sort :  forall e s u T, e |-- Srt_l s -> u : T -> 
  u = Srt_l s /\ T = Srt_l kind.
Admitted. (*
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
*)
Lemma inv_lift_ref : forall t n, llift 1 t = Ref_l n -> exists n', t = Ref_l n' /\ S n' = n.
Proof.
  induction t ; simpl ; intros ; try discriminate ; auto with coc.
  unfold llift in H ; simpl in H.
  inversion H.
  exists n ; intuition.
Qed.

(*
Lemma generation_var_aux : forall e T A, e |-- T : A -> 
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
*)
Lemma generation_var : forall e n X A, e |-- Ref_l n -> X : A -> 
  X = Ref_l n /\
  exists B, item_llift B e n /\ 
  equiv e A B.
Admitted.
(*
Proof.
  intros ; eapply generation_var_aux ; auto ; auto.
Qed.


Lemma generation_prod_depth_aux : forall e T A, e |-- T : A -> forall U V, T = Prod U V ->
  exists s1, exists s2, e |-- U : Srt s1 /\ U :: e |-- V : Srt s2 /\ equiv e A (Srt s2).
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
*)

Lemma generation_prod_depth : forall e U V X A n, e |-- Prod_l U V -> X : A [n] -> 
  exists3 U' s1 m, exists3 V' s2 p, 
  e |-- U -> U' : Srt_l s1 [m] /\ m < n /\
  U :: e |-- V -> V' : Srt_l s2 [p] /\ p < n /\
  X = Prod_l U' V' /\ equiv e A (Srt_l s2).
Admitted.
(*
Proof.
  intros ; eapply generation_prod_depth_aux ; auto ; auto.
Qed.
*)
Lemma generation_prod : forall e U V X A, e |-- Prod_l U V -> X : A -> 
  exists2 U' s1, exists2 V' s2, 
  e |-- U -> U' : Srt_l s1 /\
  U :: e |-- V -> V' : Srt_l s2 /\
  X = Prod_l U' V' /\ equiv e A (Srt_l s2).
Proof.
  intros.
  pose (tod H) ; destruct_exists.
  pose (generation_prod_depth H0) ; destruct_exists.
  exists a b ; exists a0 b0 ; intuition ; eauto with coc.
Qed.


(*


Lemma generation_sum_depth_aux : forall e T A, e |-- T : A -> forall U V, T = Sum U V ->
  exists s1, exists s2, exists s3,
  e |-- U : Srt s1 /\ 
  U :: e |-- V : Srt s2 /\
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
*)

Lemma generation_sum_depth : forall e U V X A m, e |-- Sum_l U V -> X : A [m] -> 
  exists3 U' s1 n, 
  exists3 V' s2 p, exists s3,
  e |-- U -> U' : Srt_l s1 [n] /\ n < m /\
  U :: e |-- V -> V' : Srt_l s2 [p] /\ p < m /\
  sum_sort s1 s2 s3 /\
  X = Sum_l U' V' /\ equiv e A (Srt_l s3).
Admitted.
(*
Proof.
  intros ; eapply generation_sum_depth_aux ; auto ; auto.
Qed.
*)

Lemma generation_sum : forall e U V X A, e |-- Sum_l U V -> X : A -> 
  exists2 U' s1, 
  exists2 V' s2, exists s3,
  e |-- U -> U' : Srt_l s1 /\
  U :: e |-- V -> V' : Srt_l s2 /\
  sum_sort s1 s2 s3 /\
  X = Sum_l U' V' /\ equiv e A (Srt_l s3).
Proof.
  intros.
  pose (tod H) ; destruct_exists.
  pose (generation_sum_depth H0) ; destruct_exists.
  exists a b ; exists a0 b0 ; exists x0 ; intuition ; eauto with coc.
Qed.

Lemma generation_lambda_depth_aux : forall e t X A m, e |-- t -> X : A [m] -> forall T M, t = Abs_l T M ->
  exists3 T' s1 n, exists3 M' s2 p, exists3 C C' q,
  e |-- T -> T' : Srt_l s1 [n] /\ n < m /\
  T :: e |-- M -> M' : C [p] /\ p < m /\
  T :: e |-- C -> C' : Srt_l s2 [q] /\ q < m /\
  X = Abs_l T' M' /\ equiv_sort e A  (Prod_l T C) s2.
Admitted.
(*Proof.
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
*)

Lemma generation_lambda_depth : forall e T M X A m, e |-- Abs_l T M -> X : A [m] -> 
  exists3 T' s1 n, exists3 M' s2 p, exists3 C C' q,
  e |-- T -> T' : Srt_l s1 [n] /\ n < m /\
  T :: e |-- M -> M' : C [p] /\ p < m /\
  T :: e |-- C -> C' : Srt_l s2 [q] /\ q < m /\
  X = Abs_l T' M' /\ equiv_sort e A  (Prod_l T C) s2.
Admitted.
(*
Proof.
  intros ; eapply generation_lambda_depth_aux ; auto ; auto.
Qed.
*)
Lemma generation_lambda : forall e T M X A, e |-- Abs_l T M -> X : A-> 
  exists2 T' s1, 
  exists2 M' s2,
  exists2 C C',
  e |-- T -> T' : Srt_l s1 /\
  T :: e |-- M -> M' : C /\
  T :: e |-- C -> C' : Srt_l s2 /\
  X = Abs_l T' M' /\ equiv_sort e A  (Prod_l T C) s2.
Proof.
  intros.
  pose (tod H) ; destruct_exists.
  pose (generation_lambda_depth H0) ; destruct_exists.
  exists a b ; exists a0 b0 ; exists a1 b1 ; intuition ; eauto with coc.
Qed.

Lemma generation_app_depth_aux :
forall e t Y Z m, e |-- t -> Y : Z [m] -> forall V W X, t = App_l V W X ->
  exists4 U U' s1 n,
  exists3 V' s2 p,
  exists2 X' q,
  e |-- U -> U' : Srt_l s1 [n] /\ n < m /\
  U :: e |-- V -> V' : Srt_l s2 [p] /\ p < m /\
  e |-- X -> X' : U [q] /\ q < m /\
  equiv_sort e Z (lsubst X V) s2 /\
  ((exists2 W' r, e |-- W -> W' : Prod_l U V [r] /\ r < m /\
  Y = App_l V' W' X') \/
  (exists3 T T' r, 
  W = Abs_l U T /\
  U :: e |-- T -> T' : V [r] /\ r < m /\
  Y = lsubst X' T')).
Proof.
Admitted.
(*
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
*)

Lemma generation_app_depth : forall e V W X Y Z m, e |-- App_l V W X -> Y : Z [m] -> 
  exists4 U U' s1 n,
  exists3 V' s2 p,
  exists2 X' q,
  e |-- U -> U' : Srt_l s1 [n] /\ n < m /\
  U :: e |-- V -> V' : Srt_l s2 [p] /\ p < m /\
  e |-- X -> X' : U [q] /\ q < m /\
  equiv_sort e Z (lsubst X V) s2 /\
  ((exists2 W' r, e |-- W -> W' : Prod_l U V [r] /\ r < m /\
  Y = App_l V' W' X') \/
  (exists3 T T' r, 
  W = Abs_l U T /\
  U :: e |-- T -> T' : V [r] /\ r < m /\
  Y = lsubst X' T')).
Admitted.
(*
Proof.
  intros ; eapply generation_app_depth_aux ; auto ; auto.
Qed.
*)

Lemma generation_app : forall e V W X Y Z, e |-- App_l V W X -> Y : Z -> 
  exists3 U U' s1,
  exists2 V' s2,
  exists X',
  e |-- U -> U' : Srt_l s1 /\
  U :: e |-- V -> V' : Srt_l s2 /\
  e |-- X -> X' : U /\
  equiv_sort e Z (lsubst X V) s2 /\
  ((exists W', e |-- W -> W' : Prod_l U V /\
  Y = App_l V' W' X') \/
  (exists2 T T', 
  W = Abs_l U T /\
  U :: e |-- T -> T' : V /\ Y = lsubst X' T')).
Proof.
  intros.
  pose (tod H) ; destruct_exists.
  pose (generation_app_depth H0) ; destruct_exists.
  exists a b c ; exists a0 b0 ; exists a1 ; intuition ; destruct_exists ; eauto with coc.
  right ; exists a2 b2 ; intuition ; eauto with coc.
Qed.

Lemma generation_app2 : forall e V W X Y Z, e |-- App_l V W X -> Y : Z -> 
  exists3 U U' s1,
  exists2 V' s2,
  exists2 X' W',
  e |-- U -> U' : Srt_l s1 /\
  U :: e |-- V -> V' : Srt_l s2 /\
  e |-- W -> W' : Prod_l U V 	/\
  e |-- X -> X' : U /\
  equiv_sort e Z (lsubst X V) s2 /\
  ((Y = App_l V' W' X') \/
  (exists2 T T', 
  W = Abs_l U T /\
  U :: e |-- T -> T' : V /\ Y = lsubst X' T')).
Proof.
Admitted.

(*

Lemma generation_pair_depth_aux : forall e t C, e |-- t : C -> forall T M N, t = Pair T M N ->
  exists A, exists B, exists s1, exists s2, exists s3,
  T = Sum A B /\
  e |-- A : Srt s1 /\
  A :: e |-- B : Srt s2 /\
  sum_sort s1 s2 s3 /\
  e |-- M : A /\ 
  e |-- N : subst M B /\
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
*)

Lemma generation_pair_depth : forall e T M N X C m, e |-- Pair_l T M N -> X : C [m] ->
  exists4 A A' s1 n,
  exists4 B B' s2 p,
  exists s3,
  T = Sum_l A B /\
  e |-- A -> A' : Srt_l s1 [n] /\ n < m /\
  A :: e |-- B -> B' : Srt_l s2 [p] /\ p < m /\
  sum_sort s1 s2 s3 /\
  exists2 M' q, e |-- M -> M' : A [q] /\ q < m /\
  exists2 N' r, e |-- N -> N' : lsubst M B [r] /\ r < m /\
  X = Pair_l (Sum_l A' B') M' N' /\ equiv_sort e C (Sum_l A B) s3.
Admitted.
(*
Proof.
  intros ; eapply generation_pair_depth_aux ; auto ; auto.
Qed.
*)
Lemma generation_pair : forall e T M N X C, e |-- Pair_l T M N -> X : C ->
  exists3 A A' s1,
  exists3 B B' s2,
  exists s3,
  T = Sum_l A B /\
  e |-- A -> A' : Srt_l s1 /\
  A :: e |-- B -> B' : Srt_l s2 /\
  sum_sort s1 s2 s3 /\
  exists M', e |-- M -> M' : A /\
  exists N', e |-- N -> N' : lsubst M B /\
  X = Pair_l (Sum_l A' B') M' N' /\ equiv_sort e C (Sum_l A B) s3.
Proof.
  intros.
  pose (tod H) ; destruct_exists.
  pose (generation_pair_depth H0) ; destruct_exists.
  exists a b c ; exists a0 b0 c0 ; exists x0 ; intuition ; destruct_exists ; eauto with coc.
  exists a1 ; intuition ; eauto with coc.
Qed.

Require Import Lambda.TPOSR.MaxLemmas.

Lemma generation_pi1_depth_aux : forall e t X C m, e |-- t -> X : C [m] -> forall T M, t = Pi1_l T M ->
  exists4 A A' s1 n,
  exists4 B B' s2 p,
  exists s3,
  e |-- A -> A' : Srt_l s1 [n] /\ n < m /\
  A :: e |-- B -> B' : Srt_l s2 [p] /\ p < m /\
  exists2 A'' B'', T = Sum_l A'' B'' /\
  sum_sort s1 s2 s3 /\ equiv e C A'' /\
  ((exists3 T' M' r,
  A = A'' /\ B = B'' /\
  T' = (Sum_l A' B') /\
  e |-- M -> M' : Sum_l A B [r] /\ r < m /\
  X = Pi1_l T' M') \/
  (exists3 u u' r,
  exists2 v v',
  M = Pair_l (Sum_l A B) u v /\
  e |-- A'' ~= A : s1 /\
  A'' :: e |-- B'' ~= B : s2/\
  e |-- M -> Pair_l (Sum_l A' B') u' v' : Sum_l A B [r] /\ r < m /\
  X = u')).
Proof.
  induction 1 ; simpl ; intros ; try discriminate ; auto with coc.
  pose (IHtposrd1 _ _ H1).
  destruct_exists.
  
  exists a b c d.
  exists a0 b0 c0 d0.
  exists x.
  assert(d < S (max n m)) by (apply lt_trans with n ; auto with arith).
  assert(d0 < S (max n m)) by (apply lt_trans with n ; auto with arith).
  repeat (split ; eauto).
  exists a1 b1 ; intuition.
  apply equiv_trans with A ; auto with coc.
  right ; exists s.
  apply tposr_eq_sym ; eauto with coc.

  destruct_exists.
  left.
  assert(c1 < S (max n m)) by (apply lt_trans with n ; auto with arith).
  exists a2 b2 c1 ; intuition.
  apply equiv_trans with A ; auto with coc.
  right ; exists s ; eauto with coc.

  destruct_exists.
  right.
  assert(c1 < S (max n m)) by (apply lt_trans with n ; auto with arith).
  exists a2 b2 c1 ; exists a3 b3 ; intuition.

  pose (IHtposrd1 _ _ H1).
  destruct_exists.
  exists a b c d.
  exists a0 b0 c0 d0.
  exists x.
  assert(d < S (max n m)) by (apply lt_trans with n ; auto with arith).
  assert(d0 < S (max n m)) by (apply lt_trans with n ; auto with arith).
  repeat (split ; eauto).
  exists a1 b1 ; intuition.
  apply equiv_trans with B ; auto with coc.
  right ; exists s ; eauto with coc.

  destruct_exists.
  left.
  assert(c1 < S (max n m)) by (apply lt_trans with n ; auto with arith).
  exists a2 b2 c1 ; intuition.
  apply equiv_trans with B ; eauto with coc.
  right ; exists s ; eauto with coc.

  destruct_exists.
  right.
  assert(c1 < S (max n m)) by (apply lt_trans with n ; auto with arith).
  exists a2 b2 c1 ; exists a3 b3 ; intuition.
  
  clear IHtposrd1 IHtposrd2 IHtposrd3.
  inversion H3.
  subst.
  exists A A' s1 n.
  exists B B' s2 m.
  exists s3.
  intuition ; auto with arith.
  exists A B ; intuition.
  right ; exists s1 ; eauto with coc.
  left ; exists (Sum_l A' B') t' p ; intuition.

  clear IHtposrd1 IHtposrd2 IHtposrd3.
  inversion H5.
  subst.
  exists A A' s1 n.
  exists B B' s2 m.
  exists s3.
  intuition ; auto with arith.
  exists A'' B'' ; intuition.
  right ; exists s1 ; eauto with coc.
  
  right ; exists u u' p ; exists v v' ; intuition.
Qed.

Lemma generation_pi1_depth : forall e T M X C m, e |-- Pi1_l T M -> X : C [m] ->
  exists4 A A' s1 n,
  exists4 B B' s2 p,
  exists s3,
  e |-- A -> A' : Srt_l s1 [n] /\ n < m /\
  A :: e |-- B -> B' : Srt_l s2 [p] /\ p < m /\
  exists2 A'' B'', T = Sum_l A'' B'' /\
  sum_sort s1 s2 s3 /\ equiv e C A'' /\
  ((exists3 T' M' r,
  A = A'' /\ B = B'' /\
  T' = (Sum_l A' B') /\
  e |-- M -> M' : Sum_l A B [r] /\ r < m /\
  X = Pi1_l T' M') \/
  (exists3 u u' r,
  exists2 v v',
  M = Pair_l (Sum_l A B) u v /\
  e |-- A'' ~= A : s1 /\
  A'' :: e |-- B'' ~= B : s2/\
  e |-- M -> Pair_l (Sum_l A' B') u' v' : Sum_l A B [r] /\ r < m /\
  X = u')).
Proof.
  intros ; eapply generation_pi1_depth_aux ; auto ; auto.
Qed.

Lemma generation_pi1 : forall e T M X C, e |-- Pi1_l T M -> X : C ->
  exists3 A A' s1,
  exists3 B B' s2,
  exists s3,
  e |-- A -> A' : Srt_l s1 /\
  A :: e |-- B -> B' : Srt_l s2 /\
  exists2 A'' B'', T = Sum_l A'' B'' /\
  sum_sort s1 s2 s3 /\ equiv e C A'' /\
  ((exists2 T' M',
  A = A'' /\ B = B'' /\
  T' = (Sum_l A' B') /\
  e |-- M -> M' : Sum_l A B /\
  X = Pi1_l T' M') \/
  (exists2 u u',
  exists2 v v',
  M = Pair_l (Sum_l A B) u v /\
  e |-- A'' ~= A : s1 /\
  A'' :: e |-- B'' ~= B : s2 /\
  e |-- M -> Pair_l (Sum_l A' B') u' v' : Sum_l A B /\
  X = u')).
Proof.
  intros.
  pose (tod H) ; destruct_exists.
  pose (generation_pi1_depth H0) ; destruct_exists.
  exists a b c ; exists a0 b0 c0 ; exists x0 ; intuition ; destruct_exists ; eauto with coc.
  exists a1 b1 ; intuition ; eauto with coc.
  left ; exists a2 b2 ; intuition ; eauto with coc.
  exists a1 b1 ; intuition ; eauto with coc.
  right ; exists a2 b2 ; exists a3 b3 ; intuition ; eauto with coc.
Qed.

(*Lemma generation_pi2_depth_aux : forall e t C, e |-- t : C -> forall M, t = Pi2 M ->
  exists A, exists B,
  e |-- M : Sum A B /\ 
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
*)

Lemma generation_pi2_depth :
  forall e T M X C m, e |-- Pi2_l T M -> X : C [m] ->
  exists4 A A' s1 n,
  exists4 B B' s2 p,
  exists s3,
  e |-- A -> A' : Srt_l s1 [n] /\ n < m /\
  A :: e |-- B -> B' : Srt_l s2 [p] /\ p < m /\
  T = Sum_l A B /\
  sum_sort s1 s2 s3 /\ equiv e C (lsubst (Pi1_l T M) B) /\
  ((exists3 T' M' r,
  e |-- M -> M' : Sum_l A B [r] /\ r < m /\
  T' = Sum_l A' B' /\ X = Pi2_l T' M') \/
  (exists3 u u' r,
  exists3 v v' o,
  M = Pair_l (Sum_l A B) u v /\
  e |-- u -> u' : A [r] /\ r < m /\
  e |-- v -> v' : lsubst u B [o] /\ o < m /\
  X = v')).
Admitted.
(*
Proof.
  intros ; eapply generation_pi2_depth_aux ; auto ; auto.
Qed.
*)

Lemma generation_pi2 :
  forall e T M X C, e |-- Pi2_l T M -> X : C ->
  exists3 A A' s1,
  exists3 B B' s2,
  exists s3,
  e |-- A -> A' : Srt_l s1 /\
  A :: e |-- B -> B' : Srt_l s2 /\
  T = Sum_l A B /\
  sum_sort s1 s2 s3 /\ equiv e C (lsubst (Pi1_l T M) B) /\
  ((exists2 T' M',
  e |-- M -> M' : Sum_l A B /\ 
  T' = Sum_l A' B' /\ X = Pi2_l T' M') \/
  (exists2 u u',
  exists2 v v',
  M = Pair_l (Sum_l A B) u v /\
  e |-- u -> u' : A /\ 
  e |-- v -> v' : lsubst u B /\ X = v')).
Proof.
  intros.
Admitted.


Lemma generation_subset_depth : forall e U V X A m, e |-- Subset_l U V -> X : A [m] -> 
  exists2 U' n, 
  exists2 V' p, 
  e |-- U -> U' : Srt_l set [n] /\ n < m /\
  U :: e |-- V -> V' : Srt_l prop [p] /\ p < m /\
  X = Subset_l U' V' /\ equiv_sort e A (Srt_l set) kind.
Admitted.

Lemma generation_subset : forall e U V X A, e |-- Subset_l U V -> X : A -> 
  exists2 U' V', 
  e |-- U -> U' : Srt_l set /\
  U :: e |-- V -> V' : Srt_l prop /\
  X = Subset_l U' V' /\ equiv_sort e A (Srt_l set) kind.
Proof.
  intros.
  pose (tod H) ; destruct_exists.
  pose (generation_subset_depth H0) ; destruct_exists.
  exists a a0 ; intuition ; destruct_exists ; eauto with coc.
Qed.