Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.
Implicit Types e f g : lenv.

Lemma eq_eq_l :   forall e u v s, e |-- u ~= v : s -> e |-- u ~= u : s.
Proof.
  intros.
  apply tposr_eq_trans with v ; auto with coc.
Qed.

Lemma eq_eq_r :   forall e u v s, e |-- u ~= v : s -> e |-- v ~= v : s.
Proof.
  intros.
  apply tposr_eq_trans with u ; auto with coc.
Qed.

Lemma coerce_coerce_l :  forall e u v s, e |-- u >-> v : s -> e |-- u >-> u : s.
Proof.
  intros.
  apply tposr_coerce_trans with v ; auto with coc.
Qed.

Lemma coerce_coerce_r :  forall e u v s, e |-- u >-> v : s -> e |-- v >-> v : s.
Proof.
  intros.
  apply tposr_coerce_trans with u ; auto with coc.
Qed.

Hint Resolve eq_eq_l eq_eq_r coerce_coerce_l coerce_coerce_r : ecoc.

Lemma ind_left_refl : 
  (forall e u v T, e |-- u -> v : T -> e |-- u -> u : T).
Proof.
  induction 1 ; simpl ; intros ; intuition ; auto with coc.

  apply tposr_prod with s1 ; auto with coc.

  apply tposr_abs with s1 B s2 ; auto with coc.

  apply tposr_app with  A A  s1 s2 ; eauto with coc ecoc.

  apply tposr_app with A A s1 s2 ; eauto with coc ecoc.
  apply tposr_abs with s1 B s2 ; eauto with coc ecoc.
  
  apply tposr_conv with A s ; auto with coc.

  apply tposr_sum with s1 s2 ; auto with coc.

  apply tposr_pair with s1 s2 s3 ; auto with coc.

  apply tposr_pi1 with s1 s2 s3 ; eauto with coc ecoc.

  apply tposr_pi1 with s1 s2 s3; eauto with coc ecoc.

  apply tposr_pi2 with s1 s2 s3 ; eauto with coc ecoc.

  apply tposr_pi2 with s1 s2 s3 ; eauto with coc ecoc.
Qed.

Corollary refl_l : forall e u v T, e |-- u -> v : T -> e |-- u -> u : T.
Proof (ind_left_refl).

Corollary tposrp_refl_l : forall e A B T, tposrp e A B T -> e |-- A -> A : T.
Proof.
  induction 1 ; auto with coc.
  apply (refl_l H).
Qed.

Hint Resolve refl_l tposrp_refl_l : coc.