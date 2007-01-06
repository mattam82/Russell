(* -*- coq-prog-args: ("-emacs-U" "-I" "." "-R" "." "Lambda") -*- *)

Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.Terms.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Env.
Require Import Lambda.Conv_Dec.

Set Implicit Arguments.

Implicit Types i k m n : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Definition snterm := { x : term | sn x }.

Program Definition sn_ord : snterm -> snterm -> Prop := 
  fun x y => ord_norm x y.

Require Import ProofIrrelevance.

Scheme acc_dep := Induction for Acc Sort Prop.

Lemma redn_sn_wf : well_founded sn_ord.
Proof.
  red in |- *.
  induction a.
  assert (H:=wf_ord_norm x p).
  unfold sn_ord.
  induction H.
  apply Acc_intro.
  intros.
  destruct y ; simpl in *.
  apply (H0 x0 H1 s).
Qed.
  
Program Fixpoint hnf (x : snterm) { wf x sn_ord } :  { y : term | red x y } :=
  match x with
  | App x y => 
    let nf := hnf x in
    match nf with
    | Abs T v => hnf (subst y v)
    | h => App h y
    end
  | Pi1 x =>
    let nf := hnf x in
    match nf with
    | Pair T u v => hnf u
    | h => Pi1 h
    end
  | Pi2 x =>
    let nf := hnf x in
    match nf with
    | Pair T u v => hnf u
    | h => Pi2 h
    end
  | _ => x
  end.

Obligations.

Solve Obligations using simpl ; intros ; rewrite <- Heqx ; auto with coc.

Obligations.
Obligation 4. 
simpl ; intros.
destruct x ; simpl.
simpl in Heqx.
assert(subterm x0 x).
rewrite <- Heqx ; repeat constructor.
apply subterm_sn with x ; auto.
Qed.

Obligations.

Obligation 5.
  simpl ; intros.
  destruct x ; simpl.
  simpl in Heqx.
  unfold sn_ord ; simpl.
  apply subterm_ord_norm.
  rewrite <- Heqx ; repeat constructor.
Qed.

Ltac destruct_call f :=
  match goal with
    | H : ?T |- _  =>
      match T with
        context [f ?x] => destruct (f x)
      end
  end.



Obligation 6.
  destruct x ; simpl ; intros ; rewrite <- Heqx ; auto with coc.
  destruct_call hnf ; simpl in *.
  apply red_red_app ; auto with coc.
  rewrite Heqnf ; auto.
Qed.

Obligation 7.
  destruct x ; simpl ; intros ; rewrite <- Heqx ; auto with coc.
  destruct_call hnf ; simpl in * ;
  apply red_red_app ; auto with coc ;
  rewrite Heqnf ; auto.
Qed.


Obligation 8.
  destruct x ; simpl ; intros. 
  destruct_call hnf ; simpl in *.
  
  
  apply red_red_app ; auto with coc ;
  rewrite Heqnf ; auto.
  
  


rewrite Heqx ; auto with coc.
Qed.

Obligation 3.
simpl ; intros.

  constructor.
  auto with coc datatypes.
auto.
  apply redn_sn_wf.
Qed.

Require Import Coq.subtac.Utils.

Obligation 3.
  simpl ; intros until x.
  destruct x ; simpl.
  intros.
  rewrite <- Heqx.
  destruct (hnf ((x0 &?))).
  simpl in HeqHeq_id0.
  unfold transp ; simpl.
  

  applt
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






*)
