Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Set Implicit Arguments.

Fixpoint unlab (t : lterm) : term :=
  match t with
  | Srt_l s => Srt s
  | Ref_l n => Ref n
  | Abs_l T t => Abs (unlab T) (unlab t)
  | App_l T u v => App (unlab u) (unlab v)
  | Pair_l T u v => Pair (unlab T) (unlab u) (unlab v)
  | Prod_l T U => Prod (unlab T) (unlab U)
  | Sum_l T U => Sum (unlab T) (unlab U)
  | Subset_l T U => Subset (unlab T) (unlab U)
  | Pi1_l T t => Pi1 (unlab t)
  | Pi2_l T t => Pi2 (unlab t)
  end.

Fixpoint unlab_ctx (t : lenv) : env :=
  match t with
  | nil => nil
  | cons A tl => cons (unlab A) (unlab_ctx tl)
 end.

Notation "| t |" := (unlab t) (at level 70).

Lemma lab_lift_rec : forall M n k, |llift_rec n M k| = lift_rec n (|M|) k.
Proof.
  induction M ; simpl ; unfold llift, lift ; intros ; 
auto with coc ; 
try (  rewrite (IHM1 n k) ; rewrite (IHM2 n (S k)) ; auto).
  elim (le_gt_dec k n) ; simpl ; intros; auto with coc.

  rewrite (IHM2 n k) ; rewrite (IHM3 n k) ; auto.
  rewrite (IHM1 n k) ; rewrite (IHM2 n k) ; rewrite (IHM3 n k) ; auto.
  
  rewrite (IHM2 n k) ; auto.
  rewrite (IHM2 n k) ; auto.
Qed.

Lemma lab_lift : forall M n, |llift n M| = lift n (|M|).
Proof.
  intros.
  unfold llift, lift ; apply (lab_lift_rec M n 0) ; auto.
Qed.

Lemma lab_subst_rec : forall M N k, |lsubst_rec M N k| = subst_rec (|M|) (|N|) k.
Proof.
  induction N ; simpl ; unfold lsubst, subst ; intros ; auto with coc ;
  try (  rewrite (IHN1 k) ; rewrite (IHN2 (S k)) ; auto).
  unfold lsubst_rec, subst_rec.
  elim (lt_eq_lt_dec k n) ; simpl ; intros.
  destruct a; auto.
  apply lab_lift.
  auto.

  rewrite (IHN2 k) ; rewrite (IHN3 k) ; auto.
  rewrite (IHN1 k) ; rewrite (IHN2 k) ; rewrite (IHN3 k) ; auto.

  rewrite (IHN2 k) ; auto.
  rewrite (IHN2 k) ; auto.
Qed.

Lemma lab_subst : forall M N, |lsubst M N| = subst (|M|) (|N|).
Proof.
  intros.
  unfold lsubst, subst ; apply (lab_subst_rec M N 0) ; auto.
Qed.

Lemma unlab_lred : forall M N, lred1 M N -> red (|M|) (|N|).
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
  
  rewrite lab_subst.
  apply one_step_red.
  apply Lambda.Reduction.beta.
Qed.

Lemma unlab_lab_red1 : forall (M : lterm) (N : term), red1 (|M|) N -> 
  exists N', |N'| = N /\ lred1 M N'.
Proof.
  induction M ; simpl ; intros ; auto with coc.

  inversion H.

  inversion H.

  inversion H.
  destruct (IHM1 _ H3).
  exists (Abs_l x M2) ; simpl ; intuition ; rewrite H5 ; auto with coc.
  destruct (IHM2 _ H3).
  exists (Abs_l M1 x) ; simpl ; intuition ; rewrite H5 ; auto with coc.
  
  inversion H.
  destruct M2 ; simpl in H1 ; try discriminate.
  exists (lsubst M3 M2_2).
  rewrite lab_subst.
  inversion H1.
  intuition.
  
  destruct (IHM2 _ H3).
  exists (App_l M1 x M3 ) ; simpl ; intuition ; rewrite H5 ; auto with coc.
  destruct (IHM3 _ H3).
  exists (App_l M1 M2 x) ; simpl ; intuition ; rewrite H5 ; auto with coc.

  inversion H.
  destruct (IHM1 _ H4).
  exists (Pair_l x M2 M3 ) ; simpl ; intuition ; rewrite H6 ; auto with coc.
  destruct (IHM2 _ H4).
  exists (Pair_l M1 x M3) ; simpl ; intuition ; rewrite H6 ; auto with coc.
  destruct (IHM3 _ H4).
  exists (Pair_l M1 M2 x) ; simpl ; intuition ; rewrite H6 ; auto with coc.

  inversion H.
  destruct (IHM1 _ H3).
  exists (Prod_l x M2 ) ; simpl ; intuition ; rewrite H5 ; auto with coc.
  destruct (IHM2 _ H3).
  exists (Prod_l M1 x) ; simpl ; intuition ; rewrite H5 ; auto with coc.

  inversion H.
  destruct (IHM1 _ H3).
  exists (Sum_l x M2 ) ; simpl ; intuition ; rewrite H5 ; auto with coc.
  destruct (IHM2 _ H3).
  exists (Sum_l M1 x) ; simpl ; intuition ; rewrite H5 ; auto with coc.

  inversion H.
  destruct (IHM1 _ H3).
  exists (Subset_l x M2 ) ; simpl ; intuition ; rewrite H5 ; auto with coc.
  destruct (IHM2 _ H3).
  exists (Subset_l M1 x) ; simpl ; intuition ; rewrite H5 ; auto with coc.

  inversion H.
  destruct M2 ; simpl in H1 ; try discriminate.
  inversion H1.
  simpl in H.
  inversion H.
  exists M2_2 ; intuition.
  
  destruct (IHM2 _ H6).
  exists (Pi1_l M1 x) ; simpl ; intuition ; rewrite H9 ; auto with coc.

  destruct (IHM2 _ H1).
  exists (Pi1_l M1 x) ; simpl ; intuition ; rewrite H4 ; auto with coc.

  inversion H.
  destruct M2 ; simpl in H1 ; try discriminate.
  inversion H1.
  inversion H.
  exists M2_3 ; intuition.
  
  destruct (IHM2 _ H6).
  exists (Pi2_l M1 x) ; simpl ; intuition ; rewrite H9 ; auto with coc.

  destruct (IHM2 _ H1).
  exists (Pi2_l M1 x) ; simpl ; intuition ; rewrite H4 ; auto with coc.
Qed.

Lemma unlab_lab_red : forall (M : lterm) (N : term), red (|M|) N -> 
  exists N', |N'| = N /\ lred M N'.
Proof.
  induction 1.
  exists M ; intuition ; auto with coc.
  destruct IHred.
  intuition.
  rewrite <- H2 in H0.
  destruct (unlab_lab_red1 _ H0).
  exists x0 ; intuition ; auto with coc.
  apply trans_lred with x ; auto with coc.
Qed.

Lemma unlab_lab_par_red1 : forall (M : lterm) (N : term), par_red1 (|M|) N -> 
  exists N', |N'| = N /\ par_lred1 M N'.
Proof.
  induction M ; simpl ; intros ; auto with coc.
  
  inversion H.
  exists (Srt_l s) ; simpl ; intuition ; rewrite H0 ; auto.

  inversion H.
  exists (Ref_l n) ; simpl ; intuition ; rewrite H0 ; auto.

  inversion H.
  destruct (IHM1 _ H4).
  destruct (IHM2 _ H2).
  intuition.
  exists (Abs_l x x0) ; simpl ; intuition ; rewrite H5 ; rewrite H7 ; auto with coc.
  
  inversion H.
  destruct M2 ; simpl in H1 ; try discriminate.
  simpl in H0 ; inversion H0.
  rewrite H7 in H2.
  destruct (IHM3 _ H4).
  destruct (IHM2 (Abs T M')).
  simpl.
  constructor ; auto.
  rewrite H6 ; auto with coc.

  destruct H8.
  destruct x0 ; simpl in H8 ; try discriminate.
  exists (lsubst x x0_2).
  intuition.
  rewrite <- H10.
  inversion H8.
  apply lab_subst.
  
  constructor ; auto with coc.
  inversion H9.
  auto.
  
  destruct (IHM2 _ H2).
  destruct (IHM3 _ H4).
  intuition.
  exists (App_l M1 x x0 ) ; simpl ; intuition ; rewrite H7 ; rewrite H5 ; auto with coc.

  inversion H.
  destruct (IHM1 _ H3).
  destruct (IHM2 _ H5).
  destruct (IHM3 _ H6).
  intuition.
  exists (Pair_l x x0 x1 ) ; simpl ; intuition ; rewrite H10 ; rewrite H7 ; rewrite H8 ; auto with coc.

  inversion H.
  destruct (IHM1 _ H2).
  destruct (IHM2 _ H4).
  intuition.
  exists (Prod_l x x0 ) ; simpl ; intuition ; rewrite H5 ; rewrite H7 ; auto with coc.

  inversion H.
  destruct (IHM1 _ H2).
  destruct (IHM2 _ H4).
  intuition.
  exists (Sum_l x x0 ) ; simpl ; intuition ; rewrite H5 ; rewrite H7 ; auto with coc.

  inversion H.
  destruct (IHM1 _ H2).
  destruct (IHM2 _ H4).
  intuition.
  exists (Subset_l x x0 ) ; simpl ; intuition ; rewrite H5 ; rewrite H7 ; auto with coc.

  inversion H.
  destruct M2 ; simpl in H0 ; try discriminate.
  inversion H0.
  inversion H.
  destruct (IHM2 (Pair (|M2_1|) N (|M2_3|))).
  simpl ; constructor ; auto with coc.
  intuition.
  destruct x ; simpl in H12 ; try discriminate.
  inversion H12.
  exists x2 ; intuition ; try rewrite <- H15 ; auto with coc.
  inversion H13.
  constructor.
  assumption.
  
  destruct (IHM2 _ H7).
  intuition.
  exists (Pi1_l M1 x) ; simpl ; intuition ; rewrite H10 ; auto with coc.

  destruct (IHM2 _ H1).
  intuition.
  exists (Pi1_l M1 x) ; simpl ; intuition ; rewrite H4 ; auto with coc.

  inversion H.
  destruct M2 ; simpl in H0 ; try discriminate.
  inversion H0.
  inversion H.
  destruct (IHM2 (Pair (|M2_1|) (|M2_2|) N)).
  simpl ; constructor ; auto with coc.
  intuition.
  destruct x ; simpl in H12 ; try discriminate.
  inversion H12.
  exists x3 ; intuition ; try rewrite <- H16 ; auto with coc.
  inversion H13.
  constructor.
  assumption.
  
  destruct (IHM2 _ H7).
  intuition.
  exists (Pi2_l M1 x) ; simpl ; intuition ; rewrite H10 ; auto with coc.


  destruct (IHM2 _ H1).
  intuition.
  exists (Pi2_l M1 x) ; simpl ; intuition ; rewrite H4 ; auto with coc.
Qed.




