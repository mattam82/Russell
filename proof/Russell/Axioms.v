Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Substitution.
Require Import CCPD.Coercion.
Require Import CCPD.GenerationNotKind.
Require Import CCPD.GenerationCoerce.
Require Import CCPD.Generation.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Axiom unique_sort_conv : forall G A A' s1 s2, G |- A : Srt s1 -> G |- A' : Srt s2 -> conv A A' -> s1 = s2.

Lemma inv_conv_prod_sort_l : forall e U V U' V' s, e |- Prod U V : Srt s -> e |- Prod U' V' : Srt s ->
  conv (Prod U V) (Prod U' V') -> exists s1 : sort, e |- U : Srt s1 /\ e |- U' : Srt s1 .
Proof.
  intros.
  destruct (generation_prod2 H).
  destruct (generation_prod2 H0).
  destruct H2 ; destruct H4.
  pose (inv_conv_prod_l _ _ _ _ H1).
  pose (inv_conv_prod_r _ _ _ _ H1).
  pose (unique_sort_conv H2 H4 c).
  exists x.
  split ; intuition.
  rewrite e0 ; assumption.
Qed.

Lemma inv_conv_prod_sort_r : forall e U V U' V' s, e |- Prod U V : Srt s -> e |- Prod U' V' : Srt s ->
  conv (Prod U V) (Prod U' V') -> U' :: e |- V : Srt s /\ U' :: e |- V' : Srt s. 
Proof.
  intros.
  destruct (generation_prod2 H).
  destruct (generation_prod2 H0).
  destruct H2 ; destruct H4.
  pose (inv_conv_prod_l _ _ _ _ H1).
  pose (inv_conv_prod_r _ _ _ _ H1).
  pose (unique_sort_conv H2 H4 c).
  intuition.
  apply typ_conv_env with (U :: e) ; auto with coc.
  apply coerce_env_hd with x0.
  apply coerce_conv with U' U'; auto with coc.
  rewrite <- e0 ; auto.
  apply wf_var with x0 ; auto.
Qed.

Lemma inv_conv_sum_sort : forall e U V U' V' s, e |- Sum U V : Srt s -> e |- Sum U' V' : Srt s ->
  conv (Sum U V) (Sum U' V') -> 
  exists s1, exists s2, e |- U : Srt s1 /\ e |- U' : Srt s1 /\ U :: e |- V : Srt s2 /\ U :: e |- V' : Srt s2
  /\ sum_sort s1 s2 s.	
Proof. 
  intros.
  destruct (generation_sum2 H).
  destruct (generation_sum2 H0).
  destruct H2 ; destruct H3.
  destruct H4 ; destruct H5.
  intuition.
  pose (inv_conv_sum_l _ _ _ _ H1).
  pose (inv_conv_sum_r _ _ _ _ H1).
  pose (unique_sort_conv H2 H3 c).
  rewrite <- e0 in H3.
  exists x ; exists x1 ; intuition.


  cut (U :: e |- V' : Srt x2) ; intros.
  pose (unique_sort_conv H6 H9 c0).
  rewrite e1 ; auto.

  apply typ_conv_env with (U' :: e) ; auto with coc.
  apply coerce_env_hd with x ; auto with coc.
  apply coerce_conv with U U ; auto with coc.
  apply wf_var with x ; auto with coc.
Qed.

(* Set versions of the lemmas derived from the axiom *)
Axiom inv_conv_prod_sort_l_set : forall e U V U' V' s, e |- Prod U V : Srt s -> e |- Prod U' V' : Srt s ->
  conv (Prod U V) (Prod U' V') -> { s1 : sort | e |- U : Srt s1 /\ e |- U' : Srt s1 }.


Axiom inv_conv_prod_sort_r_set : forall e U V U' V' s, e |- Prod U V : Srt s -> e |- Prod U' V' : Srt s ->
  conv (Prod U V) (Prod U' V') -> U' :: e |- V : Srt s /\ U' :: e |- V' : Srt s. 

Axiom inv_conv_sum_sort_set : forall e U V U' V' s, e |- Sum U V : Srt s -> e |- Sum U' V' : Srt s ->
  conv (Sum U V) (Sum U' V') -> 
  { s1 : sort & { s2 : sort | e |- U : Srt s1 /\ e |- U' : Srt s1 /\ U :: e |- V : Srt s2 /\ U :: e |- V' : Srt s2
  /\ sum_sort s1 s2 s}}.	

Axiom inv_conv_sum_sort_l_set : forall e U V U' V' s, e |- Sum U V : Srt s -> e |- Sum U' V' : Srt s ->
  conv (Sum U V) (Sum U' V') -> 
  { s1 : sort | e |- U : Srt s1 /\ e |- U' : Srt s1 }.

Axiom inv_conv_sum_sort_r_set : forall e U V U' V' s, e |- Sum U V : Srt s -> e |- Sum U' V' : Srt s ->
  conv (Sum U V) (Sum U' V') -> 
  { s2 : sort | U :: e |- V : Srt s2 /\ U :: e |- V' : Srt s2 }.
