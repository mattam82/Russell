Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import TPOSR.Terms.
Require Import TPOSR.Reduction.
Require Import TPOSR.Conv.
Require Import TPOSR.LiftSubst.
Require Import TPOSR.Env.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : env.

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
  | Pi1_l t => Pi1 (unlab t)
  | Pi2_l t => Pi2 (unlab t)
  | Let_in_l u v => Let_in (unlab u) (unlab v)
  end.

Fixpoint unlab_ctx (t : env) : Lambda.Env.env :=
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
  rewrite (IHM n k) ; auto.
  rewrite (IHM n k) ; auto.
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

  rewrite (IHN k) ; auto.
  rewrite (IHN k) ; auto.
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

Lemma unlab_lab_red : forall (M : lterm) (N : term), red1 (|M|) N -> 
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
  destruct M ; simpl in H1 ; try discriminate.
  inversion H1.
  inversion H.
  exists M2 ; intuition.
  
  destruct (IHM _ H6).
  exists (Pi1_l x) ; simpl ; intuition ; rewrite H9 ; auto with coc.

  destruct (IHM _ H1).
  exists (Pi1_l x) ; simpl ; intuition ; rewrite H4 ; auto with coc.

  inversion H.
  destruct M ; simpl in H1 ; try discriminate.
  inversion H1.
  inversion H.
  exists M3 ; intuition.
  
  destruct (IHM _ H6).
  exists (Pi2_l x) ; simpl ; intuition ; rewrite H9 ; auto with coc.

  destruct (IHM _ H1).
  exists (Pi2_l x) ; simpl ; intuition ; rewrite H4 ; auto with coc.

  inversion H.
  

  destruct (IHM1 _ H4).
  exists (Pair_l x M2 M3 ) ; simpl ; intuition ; rewrite H6 ; auto with coc.
  destruct (IHM2 _ H4).
  exists (Pair_l M1 x M3) ; simpl ; intuition ; rewrite H6 ; auto with coc.
  destruct (IHM3 _ H4).
  exists (Pair_l M1 M2 x) ; simpl ; intuition ; rewrite H6 ; auto with coc.






  exists (Srt_l s) ; intuition.
  inversion (red1_sort).



