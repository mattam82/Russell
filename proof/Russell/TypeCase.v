Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.Russell.Types.
Require Import Lambda.Russell.Coercion.
Require Import Lambda.Russell.Inversion.
Require Import Lambda.Russell.Thinning.
Require Import Lambda.Russell.Substitution.
Require Import Lambda.Russell.Generation.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Theorem type_case :
   forall e t T,
   typ e t T -> (exists s : sort, typ e T (Srt s)) \/ T = Srt kind.
Proof.
  intros.
  destruct (type_sorted H) ; intuition.
Qed.

  Lemma type_free_db : forall e t T, typ e t T -> free_db (length e) T.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
inversion_clear H0.
apply typ_free_db with (Srt x); auto with coc core arith datatypes.

rewrite H0; auto with coc core arith datatypes.
Qed.


(*

Definition is_redex (t : term) := 
match t with 
| (App (Abs _ _) _) => True
| _ => False
end.

Lemma is_redex_dec : forall t, is_redex t \/ ~ is_redex t.
Proof.
intros.
induction t  ; simpl ;  auto.
induction t1 ; simpl ; auto.
Qed.

Lemma is_redex_lemma: 
  forall t : term, is_redex t -> exists M, exists U, exists V, t = App (Abs M U) V.
Proof.
intros.
induction t ; simpl ; simpl in H ; auto ; intuition.
induction t1 ; simpl ; simpl in H ; auto ; intuition.
exists t1_1 ; exists t1_2 ; exists t2 ; auto.
Qed.

Inductive hnf : term -> term -> Prop :=
  | hnf_beta : forall T M U U', hnf (subst T U) U' ->  hnf (App (Abs M U) T) U'
  | hnf_pi1 : forall T U V U', hnf U U' ->  hnf (Pi1 (Pair T U V)) U'
  | hnf_pi2 : forall T U V V', hnf V V' ->  hnf (Pi2 (Pair T U V)) V'
  | hnf_other : forall T, ~ is_redex T -> hnf T T.*)
(*
Lemma hnf_injection : forall t t', t = t' -> forall u, hnf t u -> forall u', 
  hnf t' u' -> u = u'.
Proof.
intros. 
induction H0.
rewrite <- H in H1.
induction H1.


set (tfull := t).
rewrite <- H in H1.
induction t ; auto with coc core ; try solve [inversion H0 ; inversion H1 ; auto].

induction t1 ; simpl ; auto with coc core ; try solve [inversion H0 ; inversion H1 ; auto].

inversion_clear H0.
inversion_clear H1.


exists (subst t2 t1_2).
apply hnf_beta.

induction (is_redex_lemma t H).
induction H0.
induction H0.
exists (

*)
(*
Lemma hnf_conv : forall t t', hnf t t' -> conv t t'.
intros.
induction H.
apply trans_conv_conv with (subst T U) ; auto with coc core.
apply trans_conv_conv with U ; auto with coc core.
apply trans_conv_conv with V ; auto with coc core.
apply refl_conv.
Qed.

Hint Resolve hnf_conv : coc.

Definition is_subset (t : term) := 
match t with 
| (Subset _ _) => True
| _ => False
end.

Definition is_subset_dec (t : term) := 
match t with 
| (Subset _ _) => true
| _ => false
end.

Lemma is_subset_lemma : forall t : term, is_subset t \/ ~is_subset t.
Proof.
intros.
induction t ; simpl ; auto.
Qed.

Lemma is_subset_impl: forall t : term, is_subset t -> exists U, exists V, t = Subset U V.
Proof.
intros.
induction t ; simpl ; simpl in H ; auto ; intuition.
exists t1 ; exists t2 ; auto.
Qed.

Inductive mu : term -> term -> Prop :=
| mu_subset : forall T U P, hnf T (Subset U P) ->  
forall U', mu U U' -> mu T U'

   | mu_other : forall T T',  hnf T T' -> 
   ~ (exists U, exists P, T' = (Subset U P)) ->
   mu T T.

Fixpoint mu_rec (t : term) (hnf : term -> term) { struct t }: term :=
  match t with
    Subset U P => mu_rec U hnf
    | _ => t
 end.

Lemma hnf_red : forall T T' U U', red T U -> hnf T T' -> hnf U U' -> conv T' U'.
Proof.
  intros.
  apply trans_conv_conv with T ; auto with coc.
  apply sym_conv ; auto with coc.
  apply trans_conv_conv with U ; auto with coc.
Qed.*)
(*

Lemma conv_subset_hnf_subset : forall A U P, conv A (Subset U P) -> 
  exists U', exists P', hnf A (Subset U' P') /\ conv U U' /\ conv P P'.
Proof.
intros.
elim church_rosser with A (Subset U P) ; intros ; auto with coc.
inversion H1.
rewrite <- H2 in H0.
inversion H0.

exists U ; exists P ; auto with coc.
split ; auto.
apply hnf_other.
red ; auto.
split ; auto with coc.

inversion H3.
inversion H4.
exists U ; exists P ; simpl ; auto.
split.
apply hnf_beta.
rewrite H9.
apply hnf_other ; auto.
split ; auto with coc.

exists U ; exists P ; simpl.
split ; simpl ; auto.
apply hnf_pi1 ; auto with coc.
apply hnf_other ; auto with coc.
split ; auto with coc.

exists U ; exists P ; simpl.
split ; simpl ; auto.
apply hnf_pi2 ; auto with coc.
apply hnf_other ; auto with coc.
split ; auto with coc.

exists M1 ; exists P.
split ; auto with coc.
apply hnf_other ; auto with coc.

exists U ; exists M2.
split ; auto with coc.
apply hnf_other ; auto with coc.

split ; auto with coc.


rewrite <- H7 in H4.
inversion H4.
*)
(*


Lemma mu_conv : forall A A', mu A A' -> forall B, conv A B -> forall B', mu B B' -> conv A' B'.
Proof.
induction 1 ; simpl ; intros.
pose (hnf_conv H).
assert (conv B (Subset U P)).
apply trans_conv_conv with T ; auto with coc core.
Admitted.*)
(*

Lemma inv_coerce_prod : forall S T, S >> T -> 
  forall A B, mu S (Prod A B) -> forall T', mu T T' -> 
  exists A', exists B', conv T' (Prod A' B').
Proof.
intros S T H; induction H ; intros ; try rewrite H0 in H ; auto with coc core ; 
try discriminate.

inversion H0.
inversion H1.
pose (trans_conv_conv A B (Subset U0 P0) H (hnf_conv _ _ H6)).
pose (trans_conv_conv _ _ _ (sym_conv _ _ (hnf_conv _ _ H2)) c).
pose (inv_conv_subset_l _ _ _ _ c0).

elim (conv_prod_subset _ _ _ _ c).

rewrite H5 in H ; auto with coc.
exists A0 ; exists B0 ; auto with coc.

inversion H2.
pose (hnf_conv _ _ H3).
elim conv_prod_subset with A' B' U P ; auto with coc core.

exists A' ; exists B' ; auto with coc.

inversion H1.
inversion H2.
rewrite <- H6 in H3.
apply (IHcoerce _ _ H0 T' H3).

inversion H2.
elim H3.
exists U' ; exists P ; auto with coc.

cut(exists x', mu B x').
intro.
induction H3.
pose (IHcoerce1 A0 B0 H1 x H3).



Lemma inv_typ_sort_set : forall G t, G |-- t : (Srt set) -> ~ conv t (Srt set).
Proof.
intros.
red ; intros.
inversion H0.
rewrite H1 in H.
pose (inv_typ_set G (Srt set) H).
inversion c.
apply conv_kind_set ; auto with coc core.
Admitted.



Lemma subset_inv : forall G U P T, G |-- Subset U P : T ->
  forall s, ~ conv U (Srt s).
Proof.
intros G U P T typUP.
apply inv_typ_subset with G U P T ; auto.
intros.
red ; intros.
Admitted.
*)
(*
Lemma coercion_sorts : forall s1 s2, Srt s1 >> Srt s2 -> s1 = s2.
Proof.
  intros.
  inversion H.
  elim (conv_sort _ _ H0) ; auto.
*)  

(*
Lemma coerce_sorts : forall G s1 Ts1 s2 Ts2, 
  Ts1 = Srt s1 -> Ts2 = Srt s2 -> G |-- Ts1 >> Ts2 -> 
  forall s, G |-- Ts1 : Srt s -> G |-- Ts2 : Srt s -> s1 = s2.
Proof.
  induction 3 ; intros ; try discriminate ; auto with coc.
  apply conv_sort.
  rewrite H in H3 ; rewrite H0 in H3 ; assumption.

  pose (IHcoerce1 H H

  rewrite H1 in H3.
  rewrite H2 in H5.
  inversion H5.
  rewrite <- H8 in H4.
  inversion H4.

Admitted.  
*)
(*
  Theorem type_case :
   forall e t T,
   typ e t T -> (exists s : sort, typ e T (Srt s)) \/ T = Srt kind.
pose (type_sorted).

induction 1; intros; auto with coc core arith datatypes.
left.
elim wf_sort_lift with n e T; auto with coc core arith datatypes; intros.
exists x; auto with coc core arith datatypes.

left.
exists s2.
apply type_prod with s1; auto with coc core arith datatypes.

left.
elim IHtyp2; intros.
elim H1; intros.
apply inv_typ_prod with e V Ur (Srt x); auto with coc core arith datatypes;
 intros.
exists s2.
replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

discriminate H1.

left.
exists s2.
apply type_sum with s1 ; auto with coc core arith datatypes.

case s2; auto with coc core arith datatypes.
left.
exists kind.
apply type_prop.
apply typ_wf with T (Srt s1); auto with coc core arith datatypes.

left.
exists kind.
apply type_set.
apply typ_wf with T (Srt s1); auto with coc core arith datatypes.

case s2.
right ; auto.
left.
exists kind ; apply type_prop.
apply typ_wf with T (Srt s1); auto with coc core arith datatypes.

left; exists kind ; apply type_set.
apply typ_wf with T (Srt s1); auto with coc core arith datatypes.

induction IHtyp.
induction H0.
apply inv_typ_sum with e U V (Srt x) ; auto with coc core arith.
intros.
left ; exists s1 ; auto with coc core arith.
discriminate H0.

induction IHtyp.
left.
induction H0.
exists x ; auto with coc core.
replace (Srt x) with (subst (Pi1 t) (Srt x)).
apply substitution with U ; auto with coc core.
apply inv_typ_sum with e U V (Srt x) ; auto with coc core arith.
intros.
rewrite <- (coerce_sorts _ _ H3).
assumption.
apply type_pi1 with V ; auto with coc core arith datatypes.
unfold subst ; simpl ; auto.
discriminate H1.

induction H5.
left.
induction H5.
exists x.
replace (Srt x) with (subst t0 (Srt x)).
apply substitution with U ; auto with coc core.
unfold subst ; simpl ; auto.
right.
rewrite H5.
unfold subst ; simpl ; auto.

induction H4.
left ; exists s ; auto.
left.
exists s ; auto.
Qed.
*)