Require Import Termes.

  Lemma lift_ref_ge :
   forall k n p, p <= n -> lift_rec k (Ref n) p = Ref (k + n).
intros; simpl in |- *.
elim (le_gt_dec p n); auto with coc core arith sets.
intro; absurd (p <= n); auto with coc core arith sets.
Qed.


  Lemma lift_ref_lt : forall k n p, p > n -> lift_rec k (Ref n) p = Ref n.
intros; simpl in |- *.
elim (le_gt_dec p n); auto with coc core arith sets.
intro; absurd (p <= n); auto with coc core arith sets.
Qed.


  Lemma subst_ref_lt : forall u n k, k > n -> subst_rec u (Ref n) k = Ref n.
simpl in |- *; intros.
elim (lt_eq_lt_dec k n); [ intro a | intro b; auto with coc core arith sets ].
elim a; clear a; [ intro a | intro b ].
absurd (k <= n); auto with coc core arith sets.

inversion_clear b in H.
elim gt_irrefl with n; auto with coc core arith sets.
Qed.


  Lemma subst_ref_gt :
   forall u n k, n > k -> subst_rec u (Ref n) k = Ref (pred n).
simpl in |- *; intros.
elim (lt_eq_lt_dec k n); [ intro a | intro b ].
elim a; clear a; [ intro a; auto with coc core arith sets | intro b ].
inversion_clear b in H.
elim gt_irrefl with n; auto with coc core arith sets.

absurd (k <= n); auto with coc core arith sets.
Qed.


  Lemma subst_ref_eq : forall u n, subst_rec u (Ref n) n = lift n u.
intros; simpl in |- *.
elim (lt_eq_lt_dec n n); [ intro a | intro b ].
elim a; intros; auto with coc core arith sets.
elim lt_irrefl with n; auto with coc core arith sets.

elim gt_irrefl with n; auto with coc core arith sets.
Qed.



  Lemma lift_rec0 : forall M k, lift_rec 0 M k = M.
simple induction M; simpl in |- *; intros; auto with coc core arith sets ;
try (try rewrite H; try rewrite H0 ; try rewrite H1 ; auto with coc core arith sets).
elim (le_gt_dec k n); auto with coc core arith sets.
Qed.

Lemma lift0 : forall M, lift 0 M = M.
intros; unfold lift in |- *.
apply lift_rec0; auto with coc core arith sets.
Qed.


  Lemma simpl_lift_rec :
   forall M n k p i,
   i <= k + n ->
   k <= i -> lift_rec p (lift_rec n M k) i = lift_rec (p + n) M k.
simple induction M; simpl in |- *; intros; auto with coc core arith sets ; 
  try (rewrite H; auto with coc core arith sets; rewrite H0; try rewrite H1 ; simpl in |- *;
 auto with coc core arith sets).

elim (le_gt_dec k n); intros.
rewrite lift_ref_ge; auto with coc core arith sets.

rewrite plus_comm; apply le_trans with (k + n0);
 auto with coc core arith sets.

rewrite lift_ref_lt; auto with coc core arith sets.
apply le_gt_trans with k; auto with coc core arith sets.
Qed.


  Lemma simpl_lift : forall M n, lift (S n) M = lift 1 (lift n M).
intros; unfold lift in |- *.
rewrite simpl_lift_rec; auto with coc core arith sets.
Qed.

Lemma permute_lift_rec :
   forall M n k p i,
   i <= k ->
   lift_rec p (lift_rec n M k) i = lift_rec n (lift_rec p M i) (p + k).
simple induction M; simpl in |- *; intros; auto with coc core arith sets ;
 try (
rewrite H; auto with coc core arith sets; rewrite H0; try rewrite H1 ;
 auto with coc core arith sets ; repeat (rewrite plus_n_Sm; auto with coc core arith sets)).
elim (le_gt_dec k n); elim (le_gt_dec i n); intros.
rewrite lift_ref_ge; auto with coc core arith sets.
rewrite lift_ref_ge; auto with coc core arith sets.
elim plus_assoc_reverse with p n0 n.
elim plus_assoc_reverse with n0 p n.
elim plus_comm with p n0; auto with coc core arith sets.

apply le_trans with n; auto with coc core arith sets.

absurd (i <= n); auto with coc core arith sets.
apply le_trans with k; auto with coc core arith sets.

rewrite lift_ref_ge; auto with coc core arith sets.
rewrite lift_ref_lt; auto with coc core arith sets.

rewrite lift_ref_lt; auto with coc core arith sets.
rewrite lift_ref_lt; auto with coc core arith sets.
apply le_gt_trans with k; auto with coc core arith sets.
Qed.


  Lemma permute_lift :
   forall M k, lift 1 (lift_rec 1 M k) = lift_rec 1 (lift 1 M) (S k).
intros.
change (lift_rec 1 (lift_rec 1 M k) 0 = lift_rec 1 (lift_rec 1 M 0) (1 + k))
 in |- *.
apply permute_lift_rec; auto with coc core arith sets.
Qed.

Require Import Omega.

  Lemma simpl_subst_rec :
   forall M N n p k,
   p <= n + k ->
   k <= p -> subst_rec N (lift_rec (S n) M k) p = lift_rec n M k.
simple induction M; simpl in |- *; intros; auto with coc core arith sets ; 
  try (rewrite H; auto with coc core arith sets; rewrite H0; try rewrite H1;
 auto with coc core arith sets ;
 try (elim plus_n_Sm with n k; auto with coc core arith sets)).


elim (le_gt_dec k n); intros.
rewrite subst_ref_gt; auto with coc core arith sets.
red in |- *; red in |- *.
apply le_trans with (S (n0 + k)); auto with coc core arith sets.

rewrite subst_ref_lt; auto with coc core arith sets.
apply le_gt_trans with k; auto with coc core arith sets.
Qed.


  Lemma simpl_subst :
   forall N M n p, p <= n -> subst_rec N (lift (S n) M) p = lift n M.
intros; unfold lift in |- *.
apply simpl_subst_rec; auto with coc core arith sets.
Qed.


  Lemma commut_lift_subst_rec :
   forall M N n p k,
   k <= p ->
   lift_rec n (subst_rec N M p) k = subst_rec N (lift_rec n M k) (n + p).
simple induction M; intros; auto with coc core arith sets ; 
 try (simpl in |- *; rewrite H; auto with coc core arith sets; rewrite H0; try rewrite H1 ;
 auto with coc core arith sets ; rewrite plus_n_Sm ; auto with coc core arith sets).

unfold subst_rec at 1, lift_rec at 2 in |- *.
elim (lt_eq_lt_dec p n);
 [ intro Hlt_eq; elim (le_gt_dec k n); [ intro Hle | intro Hgt ]
 | intro Hlt; elim (le_gt_dec k n); [ intro Hle | intro Hgt ] ].
elim Hlt_eq; clear Hlt_eq.
case n; [ intro Hlt | intros ].
inversion_clear Hlt.

unfold pred in |- *.
rewrite lift_ref_ge; auto with coc core arith sets.
rewrite subst_ref_gt; auto with coc core arith sets.
elim plus_n_Sm with n0 n1.
auto with coc core arith sets.

apply le_trans with p; auto with coc core arith sets.

simple induction 1.
rewrite subst_ref_eq.
unfold lift in |- *.
rewrite simpl_lift_rec; auto with coc core arith sets.

absurd (k <= n); auto with coc core arith sets.
apply le_trans with p; auto with coc core arith sets.
elim Hlt_eq; auto with coc core arith sets.
simple induction 1; auto with coc core arith sets.

rewrite lift_ref_ge; auto with coc core arith sets.
rewrite subst_ref_lt; auto with coc core arith sets.

rewrite lift_ref_lt; auto with coc core arith sets.
rewrite subst_ref_lt; auto with coc core arith sets.
apply le_gt_trans with p; auto with coc core arith sets.
Qed.


  Lemma commut_lift_subst :
   forall M N k, subst_rec N (lift 1 M) (S k) = lift 1 (subst_rec N M k).
intros; unfold lift in |- *.
rewrite commut_lift_subst_rec; auto with coc core arith sets.
Qed.


  Lemma distr_lift_subst_rec :
   forall M N n p k,
   lift_rec n (subst_rec N M p) (p + k) =
   subst_rec (lift_rec n N k) (lift_rec n M (S (p + k))) p.
simple induction M; intros; auto with coc core arith sets ; try (
simpl in |- *; try replace (S (p + k)) with (S p + k);
 auto with coc core arith sets ;
rewrite H; try rewrite H0; try rewrite H1 ; auto with coc core arith sets).

unfold subst_rec at 1 in |- *.
elim (lt_eq_lt_dec p n); [ intro a | intro b ].
elim a; clear a.
case n; [ intro a | intros n1 b ].
inversion_clear a.

unfold pred, lift_rec at 1 in |- *.
elim (le_gt_dec (p + k) n1); intro.
rewrite lift_ref_ge; auto with coc core arith sets.
elim plus_n_Sm with n0 n1.
rewrite subst_ref_gt; auto with coc core arith sets.
red in |- *; red in |- *; apply le_n_S.
apply le_trans with (n0 + (p + k)); auto with coc core arith sets.
apply le_trans with (p + k); auto with coc core arith sets.

rewrite lift_ref_lt; auto with coc core arith sets.
rewrite subst_ref_gt; auto with coc core arith sets.

simple induction 1.
unfold lift in |- *.
rewrite <- permute_lift_rec; auto with coc core arith sets.
rewrite lift_ref_lt; auto with coc core arith sets.
rewrite subst_ref_eq; auto with coc core arith sets.

rewrite lift_ref_lt; auto with coc core arith sets.
rewrite lift_ref_lt; auto with coc core arith sets.
rewrite subst_ref_lt; auto with coc core arith sets.
Qed.

Lemma distr_lift_subst :
   forall M N n k,
   lift_rec n (subst N M) k = subst (lift_rec n N k) (lift_rec n M (S k)).
intros; unfold subst in |- *.
pattern k at 1 3 in |- *.
replace k with (0 + k); auto with coc core arith sets.
apply distr_lift_subst_rec.
Qed.


  Lemma distr_subst_rec :
   forall M N (P : term) n p,
   subst_rec P (subst_rec N M p) (p + n) =
   subst_rec (subst_rec P N n) (subst_rec P M (S (p + n))) p.
  simple induction M; auto with coc core arith sets; intros ; try
  (simpl in |- *; replace (S (p + n)) with (S p + n);
 auto with coc core arith sets ;
rewrite H; try rewrite H0; try rewrite H1 ; auto with coc core arith sets).

unfold subst_rec at 2 in |- *.
elim (lt_eq_lt_dec p n); [ intro Hlt_eq | intro Hlt ].
elim Hlt_eq; clear Hlt_eq.
case n; [ intro Hlt | intros n1 Heq1 ].
inversion_clear Hlt.

unfold pred, subst_rec at 1 in |- *.
elim (lt_eq_lt_dec (p + n0) n1); [ intro Hlt_eq | intro Hlt ].
elim Hlt_eq; clear Hlt_eq.
case n1; [ intro Hlt | intros n2 Heq2 ].
inversion_clear Hlt.

rewrite subst_ref_gt; auto with coc core arith sets.
rewrite subst_ref_gt; auto with coc core arith sets.
apply gt_le_trans with (p + n0); auto with coc core arith sets.

simple induction 1.
rewrite subst_ref_eq; auto with coc core arith sets.
rewrite simpl_subst; auto with coc core arith sets.

rewrite subst_ref_lt; auto with coc core arith sets.
rewrite subst_ref_gt; auto with coc core arith sets.

simple induction 1.
rewrite subst_ref_lt; auto with coc core arith sets.
rewrite subst_ref_eq.
unfold lift in |- *.
rewrite commut_lift_subst_rec; auto with coc core arith sets.

do 3 (rewrite subst_ref_lt; auto with coc core arith sets).
Qed.


  Lemma distr_subst :
   forall (P : term) N M k,
   subst_rec P (subst N M) k = subst (subst_rec P N k) (subst_rec P M (S k)).
intros; unfold subst in |- *.
pattern k at 1 3 in |- *.
replace k with (0 + k); auto with coc core arith sets.
apply distr_subst_rec.
Qed.
