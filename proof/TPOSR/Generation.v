Require Import TPOSR.Terms.
Require Import TPOSR.Reduction.
Require Import TPOSR.Conv.
Require Import TPOSR.LiftSubst.
Require Import TPOSR.Env.
Require Import TPOSR.Types.
Require Import TPOSR.Basic.
Require Import TPOSR.Substitution.
Require Import TPOSR.CtxConversion.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Definition equiv e A B s := e |- A ~= B : s.

Lemma generation_sort :  forall e s u T, e |- Srt_l s -> u : T -> 
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
Lemma generation_var_aux : forall e T A, e |- T : A -> 
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
Lemma generation_var : forall e n X A, e |- Ref_l n -> X : A -> 
  X = Ref_l n /\
  exists B, item_llift B e n /\ 
  exists s, equiv e A B s.
Admitted.
(*
Proof.
  intros ; eapply generation_var_aux ; auto ; auto.
Qed.


Lemma generation_prod_aux : forall e T A, e |- T : A -> forall U V, T = Prod U V ->
  exists s1, exists s2, e |- U : Srt s1 /\ U :: e |- V : Srt s2 /\ equiv e A (Srt s2).
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

Lemma generation_prod : forall e U V X A, e |- Prod U V -> X : A -> 
  exists s1, exists s2, e |- U : Srt s1 /\ U :: e |- V : Srt s2 /\ 
  equiv e A (Srt s2) s.
Admitted.
(*
Proof.
  intros ; eapply generation_prod_aux ; auto ; auto.
Qed.

Lemma generation_sum_aux : forall e T A, e |- T : A -> forall U V, T = Sum U V ->
  exists s1, exists s2, exists s3,
  e |- U : Srt s1 /\ 
  U :: e |- V : Srt s2 /\
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
Lemma generation_sum : forall e U V A, e |- Sum U V : A -> 
  exists s1, exists s2, exists s3,
  e |- U : Srt s1 /\ 
  U :: e |- V : Srt s2 /\
  sum_sort s1 s2 s3 /\
  equiv e A (Srt s3).
Admitted.
(*
Proof.
  intros ; eapply generation_sum_aux ; auto ; auto.
Qed.

Lemma generation_lambda_aux : forall e t A, e |- t : A -> forall T M, t = Abs T M ->
  exists s1, exists s2, exists C, 
  e |- T : Srt s1 /\ 
  T :: e |- C : Srt s2 /\
  T :: e |- M : C /\
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
*)

Lemma generation_lambda : forall e T M A, e |- Abs T M : A -> 
  exists s1, exists s2, exists C, 
  e |- T : Srt s1 /\ 
  T :: e |- C : Srt s2 /\
  T :: e |- M : C /\
  equiv e A (Prod T C).
Admitted.
(*
Proof.
  intros ; eapply generation_lambda_aux ; auto ; auto.
Qed.

Lemma generation_app_aux : forall e t C, e |- t : C -> forall M N, t = App M N ->
  exists A, exists B,
  e |- M : Prod A B /\ 
  e |- N : A /\
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
*)

Lemma generation_app : forall e M N C, e |- App M N : C -> 
  exists A, exists B,
  e |- M : Prod A B /\ 
  e |- N : A /\
  equiv e C (subst N B).
Admitted.
(*
Proof.
  intros ; eapply generation_app_aux ; auto ; auto.
Qed.


Lemma generation_pair_aux : forall e t C, e |- t : C -> forall T M N, t = Pair T M N ->
  exists A, exists B, exists s1, exists s2, exists s3,
  T = Sum A B /\
  e |- A : Srt s1 /\
  A :: e |- B : Srt s2 /\
  sum_sort s1 s2 s3 /\
  e |- M : A /\ 
  e |- N : subst M B /\
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

Lemma generation_pair : forall e T M N C, e |- Pair T M N : C ->
  exists A, exists B, exists s1, exists s2, exists s3,
  T = Sum A B /\
  e |- A : Srt s1 /\
  A :: e |- B : Srt s2 /\
  sum_sort s1 s2 s3 /\
  e |- M : A /\ 
  e |- N : subst M B /\
  equiv e C (Sum A B).
Admitted.
(*
Proof.
  intros ; eapply generation_pair_aux ; auto ; auto.
Qed.

Lemma generation_pi1_aux : forall e t C, e |- t : C -> forall M, t = Pi1 M ->
  exists A, exists B,
  e |- M : Sum A B /\ 
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
*)

Lemma generation_pi1 : forall e M C, e |- Pi1 M : C ->
  exists A, exists B,
  e |- M : Sum A B /\ 
  equiv e C A.
Admitted.
(*
Proof.
  intros ; eapply generation_pi1_aux ; auto ; auto.
Qed.

Lemma generation_pi2_aux : forall e t C, e |- t : C -> forall M, t = Pi2 M ->
  exists A, exists B,
  e |- M : Sum A B /\ 
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

Lemma generation_pi2 : forall e M C, e |- Pi2 M : C ->
  exists A, exists B,
  e |- M : Sum A B /\ 
  equiv e C (subst (Pi1 M) B).
Admitted.
(*
Proof.
  intros ; eapply generation_pi2_aux ; auto ; auto.
Qed.
*)

