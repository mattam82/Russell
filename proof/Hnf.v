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

Unset Printing All.
Program Fixpoint hnf (x : snterm) { wf x sn_ord } :  { y : term | red x y } :=
  match x with
  | App x y => 
    let nf := hnf x in
    match nf with
    | Abs T v => hnf (subst y v)
    | h => App h y
    end
  | _ => x
  end.


Solve Obligations using simpl ; intros ; rewrite <- H ; auto with coc.

Obligation 1.
  intros.
  destruct x ; simpl in * ; auto.
  apply subterm_sn with x ; auto.
  rewrite <- H ; auto with coc.
Qed.

Obligation 2.
  intros.
  unfold sn_ord ; simpl.
  constructor.
  constructor.
  destruct x ; simpl in * ; auto with coc.
  rewrite <- H ; auto with coc.
Qed.
Require Import Coq.subtac.Utils.

Obligation 3.
  intros.
  destruct_call hnf.
  simpl in *.
  destruct x ; simpl in *.
  apply sn_red_sn with (App x0 y).
  subst x ; auto.
  apply trans_red_red with (App x1 y) ; auto with coc.
  subst x1 ; auto with coc.
Qed.

Obligation 4.
  intros.
  unfold sn_ord.
  destruct x ; simpl in *.
  destruct_call hnf ; simpl in *.
  subst x x1.
  apply red_red1_ord_norm with (App (Abs T v) y) ; auto with coc.
Qed.

Obligation 5.
  intros.
  destruct_call hnf ; simpl in *.
  destruct_call hnf ; simpl in *.
  destruct x ; simpl in *.
  apply trans_red_red with (subst y v) ; auto.
  subst x x2.
  apply trans_red_red with (App (Abs T v) y) ; auto with coc.
Qed.

Obligation 6.
  intros.
  destruct x ; destruct_call hnf ; simpl in *.
  subst x x1.
  auto with coc.
Qed.

Obligation 8.
  intros.
  apply redn_sn_wf.  
Qed.

