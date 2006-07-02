
Require Import Lambda.TPOSR.Coercion.

Corollary injectivity_of_pi_coerce_aux : forall e T U s,
  e |-- T >-> U : s ->
  forall A A' B B', T = Prod_l A B -> U = Prod_l A' B' ->
  exists s1, e |-- A' >-> A : s1 /\ A' :: e |-- B >-> B' : s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc ; try discriminate.
  subst.
  pose (injectivity_of_pi H) ; destruct_exists.
  exists x.
  split ; auto with coc.
  apply coerce_conv_env with (A0 :: e) ; auto with coc.
  apply conv_env_hd with x ; auto with coc.

  inversion H5 ; inversion H6 ; subst.
  exists s ; split ; auto with coc.

  subst.
  destruct (IHtposr_coerce A' A B' B) ; auto with coc.
  destruct_exists.
  exists x ; split ; auto with coc.
  apply coerce_coerce_env with (A :: e) ; auto with coc.
  apply coerce_env_hd with x ; auto with coc.
  subst.
  destruct (IHtposr_coerce 

  
Corollary injectivity_of_pi_coerce : forall e A A' B B' s,
  e |-- Prod_l A B >-> Prod_l A' B' : s ->
  exists s1, e |-- A' >-> A : s1 /\ A' :: e |-- B >-> B' : s.
Proof.
  intros ; induction 
*)
 

Corollary injectivity_of_sum_equiv : forall e A A' B B' s, 
  e |-- Sum_l A B -> Sum_l A B : Srt_l s ->
  equiv e (Sum_l A B) (Sum_l A' B') ->
  exists2 s1 s2, e |-- A >-> A' : s1 /\ A :: e |-- B >-> B' : s2 /\ sum_sort s1 s2 s.
Proof.
  intros.
  destruct H0.
  destruct H0 ; try discriminate.
  pose (equiv_eq H H0).
  apply injectivity_of_sum.
  assumption.
Qed.
*)