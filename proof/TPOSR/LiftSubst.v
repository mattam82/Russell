Require Import TPOSR.Terms.

  Lemma llift_ref_ge :
   forall k n p, p <= n -> llift_rec k (Ref_l n) p = Ref_l (k + n).
intros; simpl in |- *.
elim (le_gt_dec p n); auto with coc core arith sets.
intro; absurd (p <= n); auto with coc core arith sets.
Qed.


  Lemma llift_ref_lt : forall k n p, p > n -> llift_rec k (Ref_l n) p = Ref_l n.
intros; simpl in |- *.
elim (le_gt_dec p n); auto with coc core arith sets.
intro; absurd (p <= n); auto with coc core arith sets.
Qed.


  Lemma lsubst_ref_lt : forall u n k, k > n -> lsubst_rec u (Ref_l n) k = Ref_l n.
simpl in |- *; intros.
elim (lt_eq_lt_dec k n); [ intro a | intro b; auto with coc core arith sets ].
elim a; clear a; [ intro a | intro b ].
absurd (k <= n); auto with coc core arith sets.

inversion_clear b in H.
elim gt_irrefl with n; auto with coc core arith sets.
Qed.


  Lemma lsubst_ref_gt :
   forall u n k, n > k -> lsubst_rec u (Ref_l n) k = Ref_l (pred n).
simpl in |- *; intros.
elim (lt_eq_lt_dec k n); [ intro a | intro b ].
elim a; clear a; [ intro a; auto with coc core arith sets | intro b ].
inversion_clear b in H.
elim gt_irrefl with n; auto with coc core arith sets.

absurd (k <= n); auto with coc core arith sets.
Qed.


  Lemma lsubst_ref_eq : forall u n, lsubst_rec u (Ref_l n) n = llift n u.
intros; simpl in |- *.
elim (lt_eq_lt_dec n n); [ intro a | intro b ].
elim a; intros; auto with coc core arith sets.
elim lt_irrefl with n; auto with coc core arith sets.

elim gt_irrefl with n; auto with coc core arith sets.
Qed.



  Lemma llift_rec0 : forall M k, llift_rec 0 M k = M.
simple induction M; simpl in |- *; intros; auto with coc core arith sets ;
try (try rewrite H; try rewrite H0 ; try rewrite H1 ; auto with coc core arith sets).
elim (le_gt_dec k n); auto with coc core arith sets.
Qed.

Lemma llift0 : forall M, llift 0 M = M.
intros; unfold llift in |- *.
apply llift_rec0; auto with coc core arith sets.
Qed.

Require Import Omega.
  Lemma simpl_llift_rec :
   forall M n k p i,
   i <= k + n ->
   k <= i -> llift_rec p (llift_rec n M k) i = llift_rec (p + n) M k.
simple induction M; simpl in |- *; intros; auto with coc core arith sets ; 
  try (rewrite H; auto with coc core arith sets; rewrite H0; try rewrite H1 ; simpl in |- *;
 auto with coc core arith sets).

elim (le_gt_dec k n); intros.
rewrite llift_ref_ge; auto with coc core arith sets.

rewrite plus_comm; apply le_trans with (k + n0);
 auto with coc core arith sets.

rewrite llift_ref_lt; auto with coc core arith sets.
apply le_gt_trans with k; auto with coc core arith sets.

rewrite H1 ; auto with arith.
rewrite H ; auto with arith.
rewrite H0 ; auto with arith.
omega.
Qed.


  Lemma simpl_llift : forall M n, llift (S n) M = llift 1 (llift n M).
intros; unfold llift in |- *.
rewrite simpl_llift_rec; auto with coc core arith sets.
Qed.

Lemma permute_llift_rec :
   forall M n k p i,
   i <= k ->
   llift_rec p (llift_rec n M k) i = llift_rec n (llift_rec p M i) (p + k).
simple induction M; simpl in |- *; intros; auto with coc core arith sets ;
 try (
rewrite H; auto with coc core arith sets; rewrite H0; try rewrite H1 ;
 auto with coc core arith sets ; repeat (rewrite plus_n_Sm; auto with coc core arith sets)).
elim (le_gt_dec k n); elim (le_gt_dec i n); intros.
rewrite llift_ref_ge; auto with coc core arith sets.
rewrite llift_ref_ge; auto with coc core arith sets.
elim plus_assoc_reverse with p n0 n.
elim plus_assoc_reverse with n0 p n.
elim plus_comm with p n0; auto with coc core arith sets.

apply le_trans with n; auto with coc core arith sets.

absurd (i <= n); auto with coc core arith sets.
apply le_trans with k; auto with coc core arith sets.

rewrite llift_ref_ge; auto with coc core arith sets.
rewrite llift_ref_lt; auto with coc core arith sets.

rewrite llift_ref_lt; auto with coc core arith sets.
rewrite llift_ref_lt; auto with coc core arith sets.
apply le_gt_trans with k; auto with coc core arith sets.
Qed.


  Lemma permute_llift :
   forall M k, llift 1 (llift_rec 1 M k) = llift_rec 1 (llift 1 M) (S k).
intros.
change (llift_rec 1 (llift_rec 1 M k) 0 = llift_rec 1 (llift_rec 1 M 0) (1 + k))
 in |- *.
apply permute_llift_rec; auto with coc core arith sets.
Qed.

Require Import Omega.

  Lemma simpl_lsubst_rec :
   forall M N n p k,
   p <= n + k ->
   k <= p -> lsubst_rec N (llift_rec (S n) M k) p = llift_rec n M k.
simple induction M; simpl in |- *; intros; auto with coc core arith sets ; 
  try (rewrite H; auto with coc core arith sets; rewrite H0; try rewrite H1;
 auto with coc core arith sets ;
 try (elim plus_n_Sm with n k; auto with coc core arith sets)).


elim (le_gt_dec k n); intros.
rewrite lsubst_ref_gt; auto with coc core arith sets.
red in |- *; red in |- *.
apply le_trans with (S (n0 + k)); auto with coc core arith sets.

rewrite lsubst_ref_lt; auto with coc core arith sets.
apply le_gt_trans with k; auto with coc core arith sets.

rewrite H ; try omega.
rewrite H0 ; try omega. 
rewrite H1 ; try omega.
reflexivity.
Qed.


  Lemma simpl_lsubst :
   forall N M n p, p <= n -> lsubst_rec N (llift (S n) M) p = llift n M.
intros; unfold llift in |- *.
apply simpl_lsubst_rec; auto with coc core arith sets.
Qed.


  Lemma commut_llift_lsubst_rec :
   forall M N n p k,
   k <= p ->
   llift_rec n (lsubst_rec N M p) k = lsubst_rec N (llift_rec n M k) (n + p).
simple induction M; intros; auto with coc core arith sets ; 
 try (simpl in |- *; rewrite H; auto with coc core arith sets; rewrite H0; try rewrite H1 ;
 auto with coc core arith sets ; rewrite plus_n_Sm ; auto with coc core arith sets).

unfold lsubst_rec at 1, llift_rec at 2 in |- *.
elim (lt_eq_lt_dec p n);
 [ intro Hlt_eq; elim (le_gt_dec k n); [ intro Hle | intro Hgt ]
 | intro Hlt; elim (le_gt_dec k n); [ intro Hle | intro Hgt ] ].
elim Hlt_eq; clear Hlt_eq.
case n; [ intro Hlt | intros ].
inversion_clear Hlt.

unfold pred in |- *.
rewrite llift_ref_ge; auto with coc core arith sets.
rewrite lsubst_ref_gt; auto with coc core arith sets.
elim plus_n_Sm with n0 n1.
auto with coc core arith sets.

apply le_trans with p; auto with coc core arith sets.

simple induction 1.
rewrite lsubst_ref_eq.
unfold llift in |- *.
rewrite simpl_llift_rec; auto with coc core arith sets.

absurd (k <= n); auto with coc core arith sets.
apply le_trans with p; auto with coc core arith sets.
elim Hlt_eq; auto with coc core arith sets.
simple induction 1; auto with coc core arith sets.

rewrite llift_ref_ge; auto with coc core arith sets.
rewrite lsubst_ref_lt; auto with coc core arith sets.

rewrite llift_ref_lt; auto with coc core arith sets.
rewrite lsubst_ref_lt; auto with coc core arith sets.
apply le_gt_trans with p; auto with coc core arith sets.
Qed.


  Lemma commut_llift_lsubst :
   forall M N k, lsubst_rec N (llift 1 M) (S k) = llift 1 (lsubst_rec N M k).
intros; unfold llift in |- *.
rewrite commut_llift_lsubst_rec; auto with coc core arith sets.
Qed.


  Lemma distr_llift_lsubst_rec :
   forall M N n p k,
   llift_rec n (lsubst_rec N M p) (p + k) =
   lsubst_rec (llift_rec n N k) (llift_rec n M (S (p + k))) p.
simple induction M; intros; auto with coc core arith sets ; try (
simpl in |- *; try replace (S (p + k)) with (S p + k);
 auto with coc core arith sets ;
rewrite H; try rewrite H0; try rewrite H1 ; auto with coc core arith sets).

unfold lsubst_rec at 1 in |- *.
elim (lt_eq_lt_dec p n); [ intro a | intro b ].
elim a; clear a.
case n; [ intro a | intros n1 b ].
inversion_clear a.

unfold pred, llift_rec at 1 in |- *.
elim (le_gt_dec (p + k) n1); intro.
rewrite llift_ref_ge; auto with coc core arith sets.
elim plus_n_Sm with n0 n1.
rewrite lsubst_ref_gt; auto with coc core arith sets.
red in |- *; red in |- *; apply le_n_S.
apply le_trans with (n0 + (p + k)); auto with coc core arith sets.
apply le_trans with (p + k); auto with coc core arith sets.

rewrite llift_ref_lt; auto with coc core arith sets.
rewrite lsubst_ref_gt; auto with coc core arith sets.

simple induction 1.
unfold llift in |- *.
rewrite <- permute_llift_rec; auto with coc core arith sets.
rewrite llift_ref_lt; auto with coc core arith sets.
rewrite lsubst_ref_eq; auto with coc core arith sets.

rewrite llift_ref_lt; auto with coc core arith sets.
rewrite llift_ref_lt; auto with coc core arith sets.
rewrite lsubst_ref_lt; auto with coc core arith sets.
Qed.

Lemma distr_llift_lsubst :
   forall M N n k,
   llift_rec n (lsubst N M) k = lsubst (llift_rec n N k) (llift_rec n M (S k)).
intros; unfold lsubst in |- *.
pattern k at 1 3 in |- *.
replace k with (0 + k); auto with coc core arith sets.
apply distr_llift_lsubst_rec.
Qed.


  Lemma distr_lsubst_rec :
   forall M N (P : lterm) n p,
   lsubst_rec P (lsubst_rec N M p) (p + n) =
   lsubst_rec (lsubst_rec P N n) (lsubst_rec P M (S (p + n))) p.
  simple induction M; auto with coc core arith sets; intros ; try
  (simpl in |- *; replace (S (p + n)) with (S p + n);
 auto with coc core arith sets ;
rewrite H; try rewrite H0; try rewrite H1 ; auto with coc core arith sets).

unfold lsubst_rec at 2 in |- *.
elim (lt_eq_lt_dec p n); [ intro Hlt_eq | intro Hlt ].
elim Hlt_eq; clear Hlt_eq.
case n; [ intro Hlt | intros n1 Heq1 ].
inversion_clear Hlt.

unfold pred, lsubst_rec at 1 in |- *.
elim (lt_eq_lt_dec (p + n0) n1); [ intro Hlt_eq | intro Hlt ].
elim Hlt_eq; clear Hlt_eq.
case n1; [ intro Hlt | intros n2 Heq2 ].
inversion_clear Hlt.

rewrite lsubst_ref_gt; auto with coc core arith sets.
rewrite lsubst_ref_gt; auto with coc core arith sets.
apply gt_le_trans with (p + n0); auto with coc core arith sets.

simple induction 1.
rewrite lsubst_ref_eq; auto with coc core arith sets.
rewrite simpl_lsubst; auto with coc core arith sets.

rewrite lsubst_ref_lt; auto with coc core arith sets.
rewrite lsubst_ref_gt; auto with coc core arith sets.

simple induction 1.
rewrite lsubst_ref_lt; auto with coc core arith sets.
rewrite lsubst_ref_eq.
unfold llift in |- *.
rewrite commut_llift_lsubst_rec; auto with coc core arith sets.

do 3 (rewrite lsubst_ref_lt; auto with coc core arith sets).
Qed.


  Lemma distr_lsubst :
   forall (P : lterm) N M k,
   lsubst_rec P (lsubst N M) k = lsubst (lsubst_rec P N k) (lsubst_rec P M (S k)).
intros; unfold lsubst in |- *.
pattern k at 1 3 in |- *.
replace k with (0 + k); auto with coc core arith sets.
apply distr_lsubst_rec.
Qed.
