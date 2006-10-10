Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.Terms.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Env.

Set Implicit Arguments.

Implicit Types i k m n : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

(*Definition head_elim (x : term) :=
  match x with
  App _ _ => True
  | Pi1 _ => True
  | Pi2 _ => True
  | _ => False
  end.

Inductive in_hnf : term -> Prop :=
  | hnf_beta : forall f, in_hnf f ->
    (forall T b, f <> Abs T b) -> forall e, in_hnf (App f e)
  | hnf_pi1 :  forall p, in_hnf p ->
    (forall T x y, p <> Pair T x y) -> 
    in_hnf (Pi1 p)
  | hnf_pi2 :  forall p, in_hnf p ->
    (forall T x y, p <> Pair T x y) -> 
    in_hnf (Pi2 p)
  | hnf_other : forall x, ~ (head_elim x) -> in_hnf x.

Lemma hnf : forall x, exists y, red x y /\ in_hnf y.
Proof.
  intros.

  induction x.

  exists (Srt s) ; split ; [auto with coc | eapply hnf_other ; red ; simpl ; intros ; auto].

  exists (Ref n) ; split ; [auto with coc | eapply hnf_other ; red ; simpl ; intros ; auto].

  exists (Abs x1 x2) ; split ; [auto with coc | eapply hnf_other ; red ; simpl ; intros ; auto].

  destruct_exists.
  destruct x0.


Fixpoint redex (x : term) :=
  match x with
  App (Abs _ _) _ => True
  | Pi1 (Pair _ _ _) => True
  | Pi2 (Pair _ _ _) => True
  | App x y => redex x 
  | Pi1 x => redex x
  | Pi2 x => redex x
  | _ => False
  end.
*)

Definition redn := transp _ red1.

Definition snterm := { x : term | sn x }.

Program Definition redn_sn : snterm -> snterm -> Prop := 
  fun x y => (transp _ red1) x y.

Definition sn_term_sn : forall t : snterm, sn (proj1_sig t).
Proof.
  destruct t ; auto.
Qed.

Scheme acc_dep := Induction for Acc Sort Prop.

Lemma well_founded_redn_sn : well_founded redn_sn.
Proof.
  red in |- *.
  cut (forall t u : snterm, redn_sn t u -> Acc redn_sn u).
  intros.
  apply H with a.

  unfold redn_sn.
  intros.
  induction a.
  unfold sn in p.
  
  induction p using acc_dep.
  pose (H x).

  inversion p.

  simpl ; intros.

  apply Acc_intro.
  intros.
  induction y.
  simpl.
  simpl in H.
  


  apply Acc_intro.
  intros.
  simpl in H0.

Program Fixpoint hnf (x : snterm) { wf x redn_sn } : term :=
  match x with
  | App x y => 
    match hnf x with
    | Abs T v => hnf (subst y v)
    | h => App h y
    end
  | Pi1 x =>
    match hnf x with
    | Pair T u v => hnf u
    | h => Pi1 h
    end
  | Pi2 x =>
    match hnf x with
    | Pair T u v => hnf u
    | h => Pi2 h
    end
  | x => x
  end.

Obligation 1.
  simpl ; intros.

  unfold well_founded.
  unfold snterm.
  intros.
  induction a.
  unfold sn in p.
  inversion p.

  apply Acc_intro.
  intros.
  unfold redn_sn in H ; simpl in H.
  inversion p.
  pose (H0 _ H).
  
  destruct y.
  
  simpl in a.
  inversion a.



Inductive hnf : term -> term -> Prop :=
  | hnf_beta : forall x, forall T e v, 
    (hnf x (Abs T e) -> 
    forall H, hnf (subst v e) H ->
    hnf (App x v) H) ->
    
  | hnf_pi1 :  forall p T x y, 
    hnf p (Pair T x y) ->
    forall H, hnf x H -> 
    hnf (Pi1 p) H
  | hnf_pi2 :  forall p T x y, hnf p (Pair T x y) ->
    forall H, hnf y H -> hnf (Pi2 p) H
  | hnf_other : forall x, ~ (exists y, hnf x y /\ y <> x) -> hnf x x.

Lemma hnf_prod : forall U V, hnf (Prod U V) (Prod U V).
Proof.
  intros.
  apply hnf_other.
  red ; intros.
  simpl in H.
  auto.
Qed.

Lemma hnf_function : forall x y z, hnf x y -> hnf x z -> y = z.
Proof.
  induction 1 ; simpl ; intros.

  inversion H1 ; subst ; auto.
  elim H2.
  simpl.
  auto.

  inversion H1 ; subst ; auto.
  elim H2.
  simpl.
  auto.

  inversion H1 ; subst ; auto.
  elim H2.
  simpl.
  auto.

  inversion H0.
  subst.
  elim H ; simpl ; auto.

  subst.
  elim H ; simpl ; auto.

  subst.
  elim H ; simpl ; auto.

  auto.
Qed.

Lemma hnf_total : forall x, exists y, hnf x y.
Proof.
  induction x.

  exists (Srt s) ; apply hnf_other ; simpl ; auto.

  exists (Ref n) ; apply hnf_other ; simpl ; auto.

  exists (Abs x1 x2) ; apply hnf_other ; simpl ; auto.

  (* App *)
  induction IHx1.
  induction x1.
  exists (Srt s) ; apply hnf_other ; simpl ; auto.







