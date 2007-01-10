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

Require Import Coq.subtac.Subtac.
Require Import Coq.subtac.FunctionalExtensionality.

Program Definition sn_ord : snterm -> snterm -> Prop := 
  fun x y => ord_norm x y.

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
Defined.

(*
Require Import Recdef.

Function hnf (x : term) { wf ord_norm x } : term :=
  match x with
    | App x y => 
      match x with
        | Abs T v => hnf (subst y v)
        | h => App h y
        end  
    | _ => x
  end.
intros.
constructor.
right.
red.
auto with coc.
unfold well_founded ; intros.
*)

Program Fixpoint hnf (x : snterm) {wf x sn_ord} :  { y : term | red x y } :=
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
        | Pair T l r => hnf l          
        | h => Pi1 h
      end
    | Pi2 x => 
      let nf := hnf x in
      match nf with
        | Pair T l r => hnf r
        | h => Pi2 h
      end
    | _ => x
  end.

Solve Obligations using simpl ; intros ; rewrite <- H ; auto with coc.

Program Lemma sn_proj_subterm_sn : forall x : snterm, forall y : term, y = x -> forall z, subterm z y -> sn z.
Proof.
  intros ; destruct x ; simpl in *.
  subst x ; apply subterm_sn with y ; auto.
Qed.

Solve Obligations using subtac_simpl ;  eapply sn_proj_subterm_sn ; eauto with coc subtac.
Require Import ZArith.

Obligation 2.
  intros.
  clear hnf.
  unfold sn_ord ; simpl.
  constructor.
  constructor.
  destruct x ; simpl in * ; auto with coc.
  rewrite <- H ; auto with coc.
Qed.

Next Obligation.
  intros.
  destruct_call hnf.
  simpl in *.
  destruct x ; simpl in *.
  subst x x1.
  apply sn_red_sn with (App x0 y) ; auto with coc.
  apply trans_red_red with (App (Abs T v) y) ; auto with coc.
Qed.

Next Obligation.
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
  unfold sn_ord ; simpl.
  constructor.
  constructor.
  destruct x ; simpl in * ; auto with coc.
  rewrite <- H ; auto with coc.
Qed.

Obligation 9 of hnf. 
  intros.
  destruct_call hnf.
  simpl in *.
  destruct x ; simpl in *.
  clear hnf.
  subst x x1.
  apply sn_red_sn with (Pi1 x0) ; auto with coc.
  apply trans_red_red with (Pi1 (Pair T l r)) ; auto with coc.
Qed.

Obligation 10.
  intros.
  unfold sn_ord.
  destruct x ; simpl in *.
  destruct_call hnf ; simpl in *.
  subst x x1.
  apply red_red1_ord_norm with (Pi1 (Pair T l r)) ; auto with coc.
Qed.

Obligation 11.
  intros.
  destruct_call hnf ; simpl in *.
  destruct_call hnf ; simpl in *.
  destruct x ; simpl in *.
  subst x x2.
  apply trans_red_red with l ; auto.
  apply trans_red_red with (Pi1 (Pair T l r)) ; auto with coc.
Qed.

Obligation 12.
  intros.
  destruct x ; destruct_call hnf ; simpl in *.
  subst x x1.
  auto with coc.
Qed.

Obligation 14.
  intros.
  unfold sn_ord ; simpl.
  constructor.
  constructor.
  destruct x ; simpl in * ; auto with coc.
  rewrite <- H ; auto with coc.
Qed.

Obligation 15 of hnf. 
  intros.
  destruct_call hnf.
  simpl in *.
  destruct x ; simpl in *.
  subst x x1.
  apply sn_red_sn with (Pi2 x0) ; auto with coc.
  apply trans_red_red with (Pi2 (Pair T l r)) ; auto with coc.
Qed.

Obligation 16.
  intros.
  unfold sn_ord.
  destruct x ; simpl in *.
  destruct_call hnf ; simpl in *.
  subst x x1.
  apply red_red1_ord_norm with (Pi2 (Pair T l r)) ; auto with coc.
Qed.

Obligation 17.
  intros.
  destruct_call hnf ; simpl in *.
  destruct_call hnf ; simpl in *.
  destruct x ; simpl in *.
  subst x x2.
  apply trans_red_red with r ; auto.
  apply trans_red_red with (Pi2 (Pair T l r)) ; auto with coc.
Qed.

Obligation 18.
  intros.
  destruct x ; destruct_call hnf ; simpl in *.
  subst x x1.
  auto with coc.
Qed.

Obligation 20.
  intros.
  apply redn_sn_wf.  
Defined.


Definition is_elim (x : term) : Prop := 
  match x with
    | App x y => True
    | Pi1 _ => True
    | Pi2 _ => True
    | _ => False
  end.

Program Lemma not_elim_hnf : forall t : snterm, ~(is_elim t) -> (`t) = hnf t.
Proof.
  intros.
  unfold hnf ; rewrite fix_sub_eq_ext.
  induction t.
  destruct x ; simpl ; auto ; simpl in H ; elim H ; auto.
Qed.  

Inductive hnf_graph : term -> term -> Prop :=
| hnf_srt : forall s, hnf_graph (Srt s) (Srt s)
| hnf_ref : forall n, hnf_graph (Ref n) (Ref n)
| hnf_abs : forall A M, hnf_graph (Abs A M) (Abs A M)
| hnf_beta : forall u T e, hnf_graph u (Abs T e) -> forall v hs, hnf_graph (subst v e) hs ->
  hnf_graph (App u v) hs
| hnf_app : forall u u', hnf_graph u u' -> (forall T e, u' <> Abs T e) -> forall v, hnf_graph (App u v) (App u' v)
| hnf_pair :
  forall T u v, hnf_graph (Pair T u v) (Pair T u v)
| hnf_prod :
  forall A B, hnf_graph (Prod A B) (Prod A B) 
| hnf_sum :
  forall A B, hnf_graph (Sum A B) (Sum A B)
| hnf_subset :
  forall A B, hnf_graph (Subset A B) (Subset A B)

| hnf_proj1 : forall p T l r, hnf_graph p (Pair T l r) -> forall l', hnf_graph l l' -> hnf_graph (Pi1 p) l'
| hnf_pi1 : forall p p', hnf_graph p p' -> (forall T l r, p' <> Pair T l r) -> hnf_graph (Pi1 p) (Pi1 p')

| hnf_proj2 : forall p T l r, hnf_graph p (Pair T l r) -> forall r', hnf_graph r r' -> hnf_graph (Pi2 p) r'
| hnf_pi2 : forall p p', hnf_graph p p' -> (forall T l r, p' <> Pair T l r) -> hnf_graph (Pi2 p) (Pi2 p').

Program Definition hnf' (x : snterm) : term := hnf x.

(*
Program Lemma hnf_graph_hnf : forall t : snterm, forall t' : term, hnf' t = t' -> hnf_graph t t'.
Proof.
  intros.
  induction t.
  unfold hnf' in H.
  simpl.
  rewrite <- H.
  clear H.
  unfold hnf.
  rewrite fix_sub_eq_ext.
  destruct x ; try (solve [(lazy beta iota delta [proj1_sig] ; lazy zeta iota beta ; try constructor)]).
  
  lazy beta iota delta [proj1_sig].
  destruct x1 ; try (solve [(lazy beta iota delta [proj1_sig] ; lazy zeta iota beta ; try constructor)]).
  
  
  

simpl in H. 

Lemma hnf_graph_total : forall t, sn t -> exists t', hnf_graph t t'.
Proof.
  intros t sn.
  elimtype (Acc ord_norm t).
  intros.
  induction x ; try solve [(eapply ex_intro ; constructor)] ; destruct_exists.
  
  assert(ord_norm x1 (App x1 x2)).
  constructor ; constructor ; auto with coc.
  pose (H0 _ H1).
  destruct_exists.
  
  set (x1' := x).
  destruct x ; try solve [(exists (App x1' x2) ; apply hnf_app ; simpl ; intros ; auto with coc ; try (red ; intros ; discriminate))].
  simpl in *.
  clear x1'.
  assert(ord_norm (subst x2 x4) (App x1 x2)).
  unfold ord_norm.
  apply t_trans with (App (Abs x3 x4) x2) ; constructor ; right ; unfold transp ; auto with coc.
*)  
