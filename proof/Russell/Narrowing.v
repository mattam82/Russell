Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Substitution.
Require Import CCPD.Depth.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Reserved Notation "G |- T >>>> U : s" (at level 70, T, U, s at next level).

Inductive coerces : env -> term -> term -> sort -> Set :=
  | coerce_refl : forall e A s, e |- A : Srt s -> e |- A >>>> A : s

  | coerce_prod : forall e A B A' B',
  forall s, e |- A' >>>> A : s ->
  (* derivable *) e |- A' : Srt s -> e |- A : Srt s ->
  forall s', (A' :: e) |- B >>>> B' : s' ->
  (* derivable *) A :: e |- B : Srt s' -> A' :: e |- B' : Srt s' ->
  e |- (Prod A B) >>>> (Prod A' B') : s'

  | coerce_sum : forall e A B A' B',
  forall s, e |- A >>>> A' : s ->
  (* derivable *) e |- A' : Srt s -> e |- A : Srt s ->
  forall s', (A :: e) |- B >>>> B' : s' ->
  (* derivable *) A :: e |- B : Srt s' -> A' :: e |- B' : Srt s' ->
  forall s'', sum_sort s s' s'' -> sum_sort s s' s'' ->
  e |- (Sum A B) >>>> (Sum A' B') : s''

  | coerce_sub_l : forall e U P U',
  e |- U >>>> U' : set ->
  (* derivable *) U :: e |- P : Srt prop ->
  e |- Subset U P >>>> U' : set

  | coerce_sub_r : forall e U U' P,
  e |- U >>>> U' : set ->
  (* derivable *) U' :: e |- P : Srt prop ->
  e |- U >>>> (Subset U' P) : set

  | coerce_conv : forall e A B C D s,
  e |- A : Srt s -> e |- B : Srt s -> e |- C : Srt s -> e |- D : Srt s ->
  conv A B -> e |- B >>>> C : s -> conv C D -> e |- A >>>> D : s

where "G |- T >>>> U : s" := (coerces G T U s).

Hint Resolve coerce_refl coerce_prod coerce_sum coerce_sub_l coerce_sub_r : coc.
Hint Resolve coerce_conv : coc.



Reserved Notation "G |- T >>> U : s" (at level 70, T, U, s at next level).

Inductive coerces_db : env -> term -> term -> sort -> Set :=
  | coerces_refl : forall e A s, e |- A : Srt s -> e |- A >>> A : s

  | coerces_prod : forall e A B A' B',
  forall s, e |- A' >>> A : s ->
  (* derivable *) e |- A' : Srt s -> e |- A : Srt s ->
  forall s', (A' :: e) |- B >>> B' : s' ->
  (* derivable *) A :: e |- B : Srt s' -> A' :: e |- B' : Srt s' ->
  e |- (Prod A B) >>> (Prod A' B') : s'

  | coerces_sum : forall e A B A' B',
  forall s, e |- A >>> A' : s ->
  (* derivable *) e |- A' : Srt s -> e |- A : Srt s ->
  forall s', (A :: e) |- B >>> B' : s' ->
  (* derivable *) A :: e |- B : Srt s' -> A' :: e |- B' : Srt s' ->
  forall s'', sum_sort s s' s'' -> sum_sort s s' s'' ->
  e |- (Sum A B) >>> (Sum A' B') : s''

  | coerces_sub_l : forall e U P U',
  e |- U >>> U' : set ->
  (* derivable *) U :: e |- P : Srt prop ->
  e |- Subset U P >>> U' : set

  | coerces_sub_r : forall e U U' P,
  e |- U >>> U' : set ->
  (* derivable *) U' :: e |- P : Srt prop ->
  e |- U >>> (Subset U' P) : set

  | coerces_conv_l : forall e A B C s,
  e |- A : Srt s -> e |- B : Srt s -> e |- C : Srt s ->
  conv A B -> e |- B >>> C : s -> e |- A >>> C : s

  | coerces_conv_r : forall e A B C s,
  e |- A : Srt s -> e |- B : Srt s -> e |- C : Srt s ->
  e |- A >>> B : s -> conv B C -> e |- A >>> C : s

where "G |- T >>> U : s" := (coerces_db G T U s).

Hint Resolve coerces_refl coerces_prod coerces_sum coerces_sub_l coerces_sub_r : coc.
Hint Resolve coerces_conv_l coerces_conv_r : coc.

Scheme coerces_db_dep := Induction for coerces_db Sort Type.

Require Import Coq.Arith.Max.
Fixpoint depth (e : env) (T U : term) (s : sort) (d : e |- T >>> U : s) {struct d}: nat :=
  match d with
  | coerces_refl e A s As => 0
  | coerces_prod e A B A' B' s HsubA A's As s' HsubBB' Bs B's =>
    S (max (depth HsubA) (depth HsubBB'))
  | coerces_sum e A B A' B' s HsubA A's As s' HsubBB' Bs B's s'' sum sum' =>
    S (max (depth HsubA) (depth HsubBB'))
  | coerces_sub_l e U P U' HsubU Ps => S (depth HsubU)
  | coerces_sub_r e U U' P HsubU Ps => S (depth HsubU)
  | coerces_conv_l e A B C s As Bs Cs convAB HsubBC => S (depth HsubBC)
  | coerces_conv_r e A B C s As Bs Cs HsubAB convBC => S (depth HsubAB)

  end.

Lemma coerces_coerces_db : forall G T U s, G |- T >>>> U : s -> G |- T >>> U : s.
Proof.
  induction 1 ; intros ; auto with coc core.

  apply coerces_prod with s; auto with coc.
  
  apply coerces_sum with s s'; auto with coc.

  apply coerces_conv_l with B ; auto with coc.
  apply coerces_conv_r with C ; auto with coc.
Qed.

Lemma coerces_db_coerces : forall G T U s, G |- T >>> U : s -> G |- T >>>> U : s.
Proof.
  induction 1 ; intros ; auto with coc core.

  apply coerce_prod with s; auto with coc.
  
  apply coerce_sum with s s'; auto with coc.

  apply coerce_conv with B C ; auto with coc.
  apply coerce_conv with A B ; auto with coc.
Qed.

Inductive coerce_in_env : env -> env -> Prop :=
  | coerce_env_hd : forall e t u s, e |- t >>> u : s -> 
	coerce_in_env (u :: e) (t :: e)
  | coerce_env_tl :
        forall e f t, wf (t :: f) -> coerce_in_env e f -> coerce_in_env (t :: e) (t :: f).

Hint Resolve coerce_env_hd coerce_env_tl: coc.

Axiom typ_conv_env :
  forall e t T, forall d : (e |- t : T),
  forall f, coerce_in_env e f -> 
  wf f -> f |- t : T.

Axiom coerce_conv_env :
  forall e T U s, forall d : (e |- T >>> U : s), 
  forall f, coerce_in_env e f -> 
  wf f -> 
	{ d' : f |- T >>> U : s | (depth d') = depth d }.


(*
Lemma conv_item :
   forall n t e,
   item_lift t e n ->
   forall f, coerce_in_env e f ->
   item_lift t f n \/
   ((forall g, trunc _ (S n) e g -> trunc _ (S n) f g) /\
   exists u, item_lift u f n /\ (exists s, f |- u >> t : s)).
simple induction n.
do 3 intro.
elim H.
do 4 intro.
rewrite H0.
inversion_clear H1.
intros.
inversion_clear H1.
right.
split; intros.
inversion_clear H1; auto with coc core arith datatypes.

exists (lift 1 t0).
split.
inversion_clear H.

unfold item_lift.
exists t0; auto with coc core arith datatypes.

exists s ; auto with coc core.
apply thinning_n_coerce with l ; auto with coc core.
apply wf_var with s.
apply coerce_sort_l with x ; auto with coc.

left.
exists x; auto with coc core arith datatypes.

do 5 intro.
elim H0.
do 4 intro.
rewrite H1.
inversion_clear H2.
intros.
inversion_clear H2.
left.
exists x; auto with coc core arith datatypes.

elim H with (lift (S n0) x) l f0; auto with coc core arith datatypes; intros.
left.
elim H2; intros.
exists x0; auto with coc core arith datatypes.
rewrite simpl_lift.
pattern (lift (S (S n0)) x0) in |- *.
rewrite simpl_lift.
elim H6; auto with coc core arith datatypes.

right.
elim H2.
clear H2.
simple induction 2; intros.
clear H6.
split; intros.
inversion_clear H6; auto with coc core arith datatypes.

destruct H7.
destruct H7.
unfold item_lift.
exists (lift 1 x0).
split ; auto with coc core.
inversion_clear H6 ; auto with coc core arith.
exists x2.
rewrite H8.
rewrite <- simpl_lift.
auto with coc core.
auto with coc.

exists x1.
pattern (lift (S (S n0)) x) ; rewrite simpl_lift.
eapply thinning_n_coerce ; auto with coc core.

exists x; auto with coc core arith datatypes.
Qed.

Lemma typ_conv_env :
  forall e t T, e |- t : T -> 
  forall f, coerce_in_env e f -> 
  wf f -> f |- t : T.
Proof.
intros e t T IH.
induction IH using typ_mut with 
(P := fun e t T => fun H : typ e t T =>
  forall f, coerce_in_env e f -> 
  wf f -> typ f t T)
(P0 := fun e T U s => fun H : e |- T >> U : s =>
  forall f, coerce_in_env e f -> 
  wf f -> f |- T >> U : s) ; intros ;
auto with coc core arith datatypes.

elim conv_item with n T e f; auto with coc core arith datatypes; intros.
repeat destruct H1.
destruct H2.
destruct H2.
destruct H3.
destruct (coerce_sort H3).
apply type_conv with x x0 ; auto with coc core.

cut (wf (T :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

cut (wf (U :: f)); intros.
apply type_pair with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.

cut (wf (T :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with V ; auto with coc core arith datatypes.

apply type_pi2 with U ; auto with coc core arith datatypes.

(*cut (wf (U :: f)); intros.
apply type_let_in with U s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.*)

apply type_conv with U s; auto with coc core arith datatypes.

cut (wf (A' :: f)) ; intros.
cut (wf (A :: f)) ; intros.
apply coerce_prod with s ;auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.

cut (wf (A' :: f)) ; intros.
cut (wf (A :: f)) ; intros.
apply coerce_sum with s ;auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.

cut (wf (U :: f)) ; intros.
apply coerce_sub_l ; auto with coc core arith datatypes.
eapply wf_var ; auto with coc core arith datatypes.
apply coerce_sort_l with U' ; auto with coc core arith datatypes.

cut (wf (U' :: f)) ; intros.
apply coerce_sub_r ; auto with coc core arith datatypes.
eapply wf_var ; auto with coc core arith datatypes.
apply coerce_sort_r with U ; auto with coc core arith datatypes.

apply coerce_conv with B C ; auto with coc core arith datatypes.
Qed.

Lemma coerce_conv_env :
  forall e T U s, e |- T >> U : s -> 
  forall f, coerce_in_env e f -> 
  wf f -> f |- T >> U : s.
Proof.
intros e T U s IH.
induction IH using coerce_mut with 
(P := fun e t T => fun H : typ e t T =>
  forall f, coerce_in_env e f -> 
  wf f -> typ f t T)
(P0 := fun e T U s => fun H : e |- T >> U : s =>
  forall f, coerce_in_env e f -> 
  wf f -> f |- T >> U : s) ; intros ;
auto with coc core arith datatypes.

elim conv_item with n T e f; auto with coc core arith datatypes; intros.
repeat destruct H1.
destruct H2.
destruct H2.
destruct H3.
destruct (coerce_sort H3).
apply type_conv with x x0 ; auto with coc core.

cut (wf (T :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

cut (wf (U :: f)); intros.
apply type_pair with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.

cut (wf (T :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with V ; auto with coc core arith datatypes.

apply type_pi2 with U ; auto with coc core arith datatypes.
(*
cut (wf (U :: f)); intros.
apply type_let_in with U s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.*)

apply type_conv with U s; auto with coc core arith datatypes.

cut (wf (A' :: f)) ; intros.
cut (wf (A :: f)) ; intros.
apply coerce_prod with s ;auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.

cut (wf (A' :: f)) ; intros.
cut (wf (A :: f)) ; intros.
apply coerce_sum with s ;auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.
apply wf_var with s ; auto with coc core arith datatypes.

cut (wf (U :: f)) ; intros.
apply coerce_sub_l ; auto with coc core arith datatypes.
eapply wf_var ; auto with coc core arith datatypes.
apply coerce_sort_l with U' ; auto with coc core arith datatypes.

cut (wf (U' :: f)) ; intros.
apply coerce_sub_r ; auto with coc core arith datatypes.
eapply wf_var ; auto with coc core arith datatypes.
apply coerce_sort_r with U ; auto with coc core arith datatypes.

apply coerce_conv with B C ; auto with coc core arith datatypes.
Qed.
*)