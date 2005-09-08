Require Import CCP.Calculus.
Require Import Omega.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

Lemma lift_add : forall t m n i, lift_rec m (lift_rec n t i) i = lift_rec (m + n) t i.
Proof.
  induction t ; intros ; unfold lift ; simpl ; auto with arith ;
    try unfold lift in IHt1, IHt2 ; try rewrite IHt1 ; try rewrite IHt2 ;
      try reflexivity.
  elim (le_gt_dec i n).
  intros.
  simpl.
  elim (le_gt_dec i (n0 + n)).
  intros ; auto with arith.
  intros. 
  assert(~ i <= n);try omega.
  contradiction.
  intros.
  simpl.
  elim (le_gt_dec i n) ; intros.
  assert(~ i <= n) ; try omega ; contradiction.
  reflexivity.
Qed.

Lemma lift_rec_0 : forall t k, lift_rec 0 t k = t.
Proof.
  induction t ; intros ; unfold lift ; simpl ; auto with arith ;
    try unfold lift in IHt1, IHt2 ; try rewrite IHt1 ; try rewrite IHt2 ;
      try reflexivity.
  elim le_gt_dec; auto.
Qed.
  
Lemma lift_0 : forall t, lift 0 t = t.
Proof.
  intros ; unfold lift ; apply lift_rec_0.
Qed.

Lemma lift_rel_ge : forall k n p, p <= n -> lift_rec k (rel n) p = rel (k + n).
Proof.
  intros ; simpl.
  elim (le_gt_dec p n) ; auto.
  intro ; absurd(p <= n) ; auto with arith.
Qed.

Lemma lift_rel_lt : forall k n p, p > n -> lift_rec k (rel n) p = rel n.
Proof.
  intros ; simpl.
  elim (le_gt_dec p n) ; auto with arith.
  intro ; absurd (p <= n) ; auto with arith.
Qed.

Lemma subst_rel_lt : forall t n k, n < k -> subst_rec t (rel n) k = rel n.
Proof.
  simpl ; intros.
  elim (lt_eq_lt_dec n k) ; intros ; auto with arith.
  elim a ; intros ; auto.
  rewrite b in H.
  absurd(k > k) ; auto with arith.
  absurd(k > n) ; auto with arith.
Qed.

Lemma subst_rel_gt : forall t n k, k < n -> subst_rec t (rel n) k = rel (pred n).
Proof.
  simpl ; intros.
  elim (lt_eq_lt_dec n k) ; intros ; auto with arith.
  elim a ; intros ; auto.
  inversion_clear a0 in H.
  absurd (S n < n) ; auto with arith.
  absurd (S n <= m) ; auto with arith.
  rewrite b in H.
  absurd(k < k) ; auto with arith.
Qed.

Lemma subst_rel_eq : forall t n, subst_rec t (rel n) n = lift n t.  
Proof.
  simpl ; intros.
  elim (lt_eq_lt_dec n n) ; intros ; auto with arith.
  elim a ; intros ; auto.
  absurd(n < n) ; auto with arith.
  absurd(n < n) ; auto with arith.
Qed.

Lemma simpl_lift_rec : forall t n k p i, i <= (k + n) -> k <= i ->
  lift_rec p (lift_rec n t k) i = lift_rec (p + n) t k.
Proof.
  induction t ; simpl ; intros; auto ; 
    try (  rewrite (IHt1) ; try rewrite (IHt2) ; simpl ; auto with arith).

  elim (le_gt_dec k n) ; intros.
  rewrite (lift_rel_ge) ; auto with arith.
  omega.

  rewrite (lift_rel_lt) ; auto with arith.
  omega.
Save.

Lemma simpl_lift : forall t n, lift (S n) t = lift 1 (lift n t).
Proof.
  intros ; unfold lift. 
  rewrite simpl_lift_rec ; auto with arith.
Save.  

Lemma permute_lift_rec : forall t n k p i, i <= k -> 
  lift_rec p (lift_rec n t k) i = lift_rec n (lift_rec p t i) (k + p).
Proof.
  induction t ; simpl ; intros; auto ; 
    try (  rewrite (IHt1) ; try rewrite (IHt2) ; simpl ; auto with arith).

  elim (le_gt_dec k n) ; intros.
  elim (le_gt_dec i n) ; intros.
  rewrite (lift_rel_ge) ; auto with arith.
  rewrite (lift_rel_ge) ; auto with arith.
  rewrite plus_permute ; reflexivity.
  omega.
  omega.
  
  absurd(i > n) ; omega.

  elim (le_gt_dec i n) ; intros ; auto with arith.
  rewrite (lift_rel_ge) ; auto with arith.
  rewrite (lift_rel_lt) ; auto with arith.
  omega.

  simpl.
  elim (le_gt_dec i n).
  intros ; absurd (i <= n) ; auto with arith.
  intros.
  elim (le_gt_dec (k + p) n) ; intros.
  absurd(k > n) ; omega.
  reflexivity.
Qed.

Lemma permute_lift : forall t k,
  lift 1 (lift_rec 1 t k) = lift_rec 1 (lift 1 t) (S k).
Proof.
  intros.
  unfold lift.
  assert(S k = k + 1).
  omega.
  rewrite H.
  apply (permute_lift_rec t 1 k 1 0).
  auto with arith.
Qed.

Lemma simpl_subst_rec : forall t u n p k, p <= n + k -> k <= p ->
  subst_rec t (lift_rec (S n) u k) p = lift_rec n u k.
Proof.
  induction u ; simpl ; intros ; auto with arith ;
    try (rewrite IHu1 ; auto with arith ; try rewrite IHu2 ; try reflexivity ; try omega).

  elim (le_gt_dec k n) ; intros ; auto.
  rewrite subst_rel_gt ; auto.
  omega.

  rewrite subst_rel_lt ; auto.
  omega.
Save.

Lemma simpl_subst : forall t u n p, p <= n ->
  subst_rec t (lift (S n) u) p = lift n u.
Proof.
  unfold subst, lift ; intros ; apply simpl_subst_rec ; auto with arith.
Qed.
  
Lemma n_plus_S_S_plus : forall n p, n + S p = (S (n + p)).
Proof.
  intros ; omega.
Qed.

Lemma commut_lift_subst_rec : forall t u n p k, k <= p ->
  lift_rec n (subst_rec u t p) k = subst_rec u (lift_rec n t k) (n + p).
Proof.
  induction t ; intros ; auto with arith ;
    try (  simpl ; rewrite IHt1 ; auto ; rewrite IHt2 ; auto) ; try omega ;
      try (rewrite n_plus_S_S_plus ; reflexivity).
  

  elim (lt_eq_lt_dec n p) ; elim (le_gt_dec k n) ; intros. 
  elim a0 ; intros.
  induction n ; intros.
  inversion_clear a1.

  rewrite lift_rel_ge ; auto with arith.
  rewrite subst_rel_lt ; auto with arith.
  rewrite subst_rel_lt ; auto with arith.
  rewrite lift_rel_ge ; auto with arith.

  assert(k = 0) ; auto with arith.
  rewrite H1.
  rewrite lift_rel_ge ; auto with arith.
  rewrite subst_rel_lt ; auto with arith.
  rewrite lift_rel_ge ; auto with arith.
  rewrite subst_rel_lt ; auto with arith.

  rewrite lift_rel_ge ; auto with arith.
  rewrite subst_rel_lt ; auto with arith.
  rewrite lift_rel_ge ; auto with arith.
  rewrite subst_rel_lt ; auto with arith.

  rewrite lift_rel_ge ; auto with arith.
  rewrite b.
  rewrite subst_rel_eq ; auto with arith.
  rewrite subst_rel_eq ; auto with arith.
  unfold lift. 
  rewrite <- lift_add.
  rewrite simpl_lift_rec ; auto with arith.
  rewrite simpl_lift_rec ; auto with arith.

  rewrite lift_rel_lt ; auto with arith.
  induction a.
  rewrite subst_rel_lt ; auto with arith.
  rewrite subst_rel_lt ; auto with arith.
  rewrite lift_rel_lt ; auto with arith.
  omega.

  rewrite <- b0 in H.
  absurd(~ k > n) ; auto with arith.

  rewrite subst_rel_gt ; auto with arith.
  rewrite lift_rel_ge ; auto with arith.
  rewrite lift_rel_ge ; auto with arith.
  rewrite subst_rel_gt ; auto with arith.
  assert(n0 + pred n = pred (n0 + n)).
  omega.
  rewrite H0.
  reflexivity.
  omega.

  absurd(p < n) ; omega.

  assert(n + (S (S p)) = (S (S (n + p)))) ; try omega.
  rewrite H0 ; reflexivity ; omega.
Save.

Lemma commut_lift_subst : forall t u k, subst_rec u (lift 1 t) (S k) = lift 1 (subst_rec u t k).
Proof.
  intros.
  unfold lift.
  rewrite commut_lift_subst_rec ; auto with arith.
Save.

Ltac rewauto x := rewrite x ; auto with arith ; try omega.

Lemma S_plus_S_plus : forall p k, S (p + k) = (S p) + k.
Proof.
  intros ; omega.
Qed.

Lemma S_S_plus_S_S_plus : forall p k, S (S (p + k)) = (S (S p)) + k.
Proof.
  intros ; omega.
Qed.

Lemma distr_lift_subst_rec: forall t u n p k,
  lift_rec n (subst_rec u t p) (p + k)
  = subst_rec (lift_rec n u k) (lift_rec n t (S (p + k))) p.
Proof.
  induction t ; intros ; auto with arith ; 
    try (simpl ; rewrite IHt1 ; try rewrite S_plus_S_plus; try rewrite S_S_plus_S_S_plus ; rewrite IHt2 ; reflexivity).

  unfold subst_rec at 1.
  elim (lt_eq_lt_dec n p).
  intros a ; elim a.
  case n ; intros.
  inversion_clear a0.

  rewauto lift_rel_lt.
  rewauto lift_rel_lt.

  rewauto lift_rel_lt.
  rewauto lift_rel_lt.
  rewauto subst_rel_lt.

  intros.
  rewrite b.
  rewauto lift_rel_lt.
  rewauto subst_rel_eq. 
  unfold lift.
  rewrite plus_comm.
  rewrite <- permute_lift_rec.
  reflexivity.
  apply (le_O_n).

  intros.
  unfold lift_rec at 1.
  elim (le_gt_dec (p + k) (pred n)).
  intros.

  rewauto lift_rel_ge.
  rewauto subst_rel_gt.
  assert(n0 + pred n = pred (n0 + n)) ; try omega ; auto with arith.

  intros.
  rewauto lift_rel_lt.
  rewauto subst_rel_gt.

  simpl.
  rewrite IHt1.
  assert(S (S (p + k)) = (S (S p)) + k); try omega.
  rewrite H.
  rewrite IHt2.
  reflexivity.
Save.  

Lemma distr_lift_subst: forall t u n k,
  lift_rec n (subst u t) k = subst (lift_rec n u k) (lift_rec n t (S k)).
Proof.
  intros.
  unfold subst.
  pattern k at 1 3.
  replace k with (0 + k); auto.
  apply distr_lift_subst_rec.
Save.


Lemma distr_subst_rec: forall t u v n p,
  subst_rec v (subst_rec u t p) (p + n)
  = subst_rec (subst_rec v u n) (subst_rec v t (S (p + n))) p.
Proof.
  induction t ; intros ; auto with arith ;
    try (simpl ; rewrite IHt1 ; 
      solve [ (rewrite S_S_plus_S_S_plus ; rewrite IHt2 ; reflexivity) |
	(rewrite S_plus_S_plus ; rewrite IHt2 ; reflexivity) ]).
  
  elim (lt_eq_lt_dec n p).
  intros.
  elim a.
  intros.
  
  do 4 (rewauto subst_rel_lt).

  intros.
  rewrite b.
  rewauto subst_rel_eq.
  rewauto subst_rel_lt.
  rewauto subst_rel_eq.
  unfold lift.
  rewauto commut_lift_subst_rec.

  intros.
  rewauto subst_rel_gt.
  unfold subst_rec at 1.
  elim (lt_eq_lt_dec (pred n) (p + n0)).
  intros.

  induction a.
  rewauto subst_rel_lt.
  rewauto subst_rel_gt.

  rewrite <- b0.
  assert(S (pred n) = n).
  omega.
  rewrite H.
  rewauto subst_rel_eq.
  unfold lift.
  assert(n = S (p + n0)).
  omega.
  rewrite H0.
  simpl.
  rewauto simpl_subst_rec.

  intros.
  rewauto (subst_rel_gt).
  rewauto (subst_rel_gt).
Save.  

Lemma distr_subst: forall v u t k,
  subst_rec v (subst u t) k = subst (subst_rec v u k) (subst_rec v t (S k)).
Proof.
  intros ; unfold subst.
  replace k with (0 + k) ; try omega.
  apply distr_subst_rec.
Save.
