
Require Export Arith.
Require Export Compare_dec.
Require Export Relations.

Implicit Types i k m n p : nat.

Section Termes.

  Inductive sort : Set :=
    | kind : sort
    | prop : sort
    | set : sort.

  Implicit Type s : sort.

  Definition is_prop s := s = prop \/ s = set.

(* Scheme to split between kind and the lower level sorts *)
  Lemma sort_level_ind :
   forall P : sort -> Prop,
   P kind -> (forall s, is_prop s -> P s) -> forall s, P s.
Proof.
unfold is_prop in |- *.
simple destruct s; auto.
Qed.

  Inductive term : Set :=
    | Srt : sort -> term
    | Ref : nat -> term
    | Abs : term -> term -> term
    | App : term -> term -> term
    | Pair : term -> term -> term -> term
    | Prod : term -> term -> term
    | Sum : term -> term -> term
    | Subset : term -> term -> term
    | Pi1 : term -> term
    | Pi2 : term -> term
    | Let_in : term -> term -> term.

  Implicit Types A B M N T t u v : term.

  Fixpoint lift_rec n t {struct t} : nat -> term :=
    fun k =>
      match t with
	| Srt s => Srt s
	| Ref i =>
          match le_gt_dec k i with
            | left _ => Ref (n + i)
            | right _ => Ref i
          end
	| Abs T M => Abs (lift_rec n T k) (lift_rec n M (S k))
	| App u v => App (lift_rec n u k) (lift_rec n v k)
	| Pair T A B => Pair (lift_rec n T k) (lift_rec n A k) (lift_rec n B k)
	| Prod A B => Prod (lift_rec n A k) (lift_rec n B (S k))
	| Sum A B => Sum (lift_rec n A k) (lift_rec n B (S k))
	| Subset A B => Subset (lift_rec n A k) (lift_rec n B (S k))
	| Pi1 A => Pi1 (lift_rec n A k)
	| Pi2 A => Pi2 (lift_rec n A k)
	| Let_in A B => Let_in (lift_rec n A k) (lift_rec n B (S k))
      end.

  Definition lift n t := lift_rec n t 0.

  Fixpoint subst_rec N M {struct M} : nat -> term :=
    fun k =>
      match M with
	| Srt s => Srt s
	| Ref i =>
          match lt_eq_lt_dec k i with
            | inleft C =>
              match C with
		| left _ => Ref (pred i)
		| right _ => lift k N
              end
            | inright _ => Ref i
          end
	| Abs A B => Abs (subst_rec N A k) (subst_rec N B (S k))
	| App u v => App (subst_rec N u k) (subst_rec N v k)
	| Pair T A B => Pair (subst_rec N T k) (subst_rec N A k) (subst_rec N B k)
	| Prod T U => Prod (subst_rec N T k) (subst_rec N U (S k))
	| Sum T U => Sum (subst_rec N T k) (subst_rec N U (S k))
	| Subset T U => Subset (subst_rec N T k) (subst_rec N U (S k))
	| Pi1 T => Pi1 (subst_rec N T k)
	| Pi2 T => Pi2 (subst_rec N T k)
	| Let_in T U => Let_in (subst_rec N T k) (subst_rec N U (S k))
    end.

  Definition subst N M := subst_rec N M 0.

  Inductive free_db : nat -> term -> Prop :=
    | db_srt : forall n s, free_db n (Srt s)
    | db_ref : forall k n, k > n -> free_db k (Ref n)
    | db_abs :
        forall k A M, free_db k A -> free_db (S k) M -> free_db k (Abs A M)
    | db_app :
        forall k u v, free_db k u -> free_db k v -> free_db k (App u v)
    | db_pair :
        forall k T u v, free_db k T -> free_db k u -> free_db k v -> free_db k (Pair T u v)
    | db_prod :
        forall k A B, free_db k A -> free_db (S k) B -> free_db k (Prod A B) 
    | db_sum :
        forall k A B, free_db k A -> free_db (S k) B -> free_db k (Sum A B)
    | db_subset :
        forall k A B, free_db k A -> free_db (S k) B -> free_db k (Subset A B)
    | db_pi1 : forall k A, free_db k A -> free_db k (Pi1 A)
    | db_pi2 : forall k A, free_db k A -> free_db k (Pi2 A)
    | db_let_in :
        forall k A B, free_db k A -> free_db (S k) B -> free_db k (Let_in A B).


  Inductive subt_bind T M : term -> Prop :=
    | Bsbt_abs : subt_bind T M (Abs T M)
    | Bsbt_prod : subt_bind T M (Prod T M)
    | Bsbt_sum : subt_bind T M (Sum T M)
    | Bsbt_subset : subt_bind T M (Subset T M)
    | Bsbt_let_in : subt_bind T M (Let_in T M).

  Inductive subt_nobind (m : term) : term -> Prop :=
    | Nbsbt_abs : forall n : term, subt_nobind m (Abs m n)
    | Nbsbt_app_l : forall v, subt_nobind m (App m v)
    | Nbsbt_app_r : forall u, subt_nobind m (App u m)
    | Nbsbt_pair_T : forall u v, subt_nobind m (Pair m u v)
    | Nbsbt_pair_l : forall T v, subt_nobind m (Pair T m v)
    | Nbsbt_pair_r : forall T u, subt_nobind m (Pair T u m)
    | Nbsbt_prod : forall n : term, subt_nobind m (Prod m n)
    | Nbsbt_sum : forall n : term, subt_nobind m (Sum m n)
    | Nbsbt_subset : forall n : term, subt_nobind m (Subset m n)
    | Nbsbt_pi1 : subt_nobind m (Pi1 m)
    | Nbsbt_pi2 : subt_nobind m (Pi2 m)
    | Nbsbt_let_in : forall n : term, subt_nobind m (Let_in m n).

  Inductive subterm (m n : term) : Prop :=
    | Sbtrm_bind : forall t, subt_bind t m n -> subterm m n
    | Sbtrm_nobind : subt_nobind m n -> subterm m n.

  Inductive mem_sort s : term -> Prop :=
    | mem_eq : mem_sort s (Srt s)
    | mem_prod_l : forall u v, mem_sort s u -> mem_sort s (Prod u v)
    | mem_prod_r : forall u v, mem_sort s v -> mem_sort s (Prod u v)
    | mem_abs_l : forall u v, mem_sort s u -> mem_sort s (Abs u v)
    | mem_abs_r : forall u v, mem_sort s v -> mem_sort s (Abs u v)
    | mem_app_l : forall u v, mem_sort s u -> mem_sort s (App u v)
    | mem_app_r : forall u v, mem_sort s v -> mem_sort s (App u v)
    | mem_pair_T : forall T u v, mem_sort s T -> mem_sort s (Pair T u v)
    | mem_pair_l : forall T u v, mem_sort s u -> mem_sort s (Pair T u v)
    | mem_pair_r : forall T u v, mem_sort s v -> mem_sort s (Pair T u v)
    | mem_sum_l : forall u v, mem_sort s u -> mem_sort s (Sum u v)
    | mem_sum_r : forall u v, mem_sort s v -> mem_sort s (Sum u v)
    | mem_subset_l : forall u v, mem_sort s u -> mem_sort s (Subset u v)
    | mem_subset_r : forall u v, mem_sort s v -> mem_sort s (Subset u v)
    | mem_pi1 : forall u, mem_sort s u -> mem_sort s (Pi1 u)
    | mem_pi2 : forall u, mem_sort s u -> mem_sort s (Pi2 u)
    | mem_let_in_l : forall u v, mem_sort s u -> mem_sort s (Let_in u v)
    | mem_let_in_r : forall u v, mem_sort s v -> mem_sort s (Let_in u v).

End Termes.

  Implicit Type s : sort.
  Implicit Types A B M N T t u v : term.

  Hint Resolve db_srt db_ref db_abs db_app db_pair db_prod db_sum db_subset db_let_in db_pi1 db_pi2 : coc.
  Hint Resolve Bsbt_abs Bsbt_prod Bsbt_sum Bsbt_subset Bsbt_let_in : coc.
  Hint Resolve Nbsbt_abs Nbsbt_app_l Nbsbt_app_r Nbsbt_pair_T Nbsbt_pair_l
    Nbsbt_pair_r Nbsbt_pi1 Nbsbt_pi2 Nbsbt_prod Nbsbt_sum Nbsbt_subset
    Nbsbt_let_in : coc.
  Hint Resolve Sbtrm_nobind: coc.
  
(*
  Hints Unfold  mem_sort : coc.
*)
  Hint Resolve mem_eq mem_prod_l mem_prod_r mem_abs_l mem_abs_r mem_app_l
    mem_app_r mem_pair_T mem_pair_l mem_pair_r : coc.
  Hint Resolve mem_sum_l mem_sum_r mem_subset_l mem_subset_r mem_pi1 mem_pi2
    mem_let_in_l mem_let_in_r : coc.

Section Beta_Reduction.

  Inductive red1 : term -> term -> Prop :=
    | beta : forall M N T, red1 (App (Abs T M) N) (subst N M)
    | pi1 : forall T M N, red1 (Pi1 (Pair T M N)) M
    | pi2 : forall T M N, red1 (Pi2 (Pair T M N)) N
    | abs_red_l :
        forall M M', red1 M M' -> forall N, red1 (Abs M N) (Abs M' N)
    | abs_red_r :
        forall M M', red1 M M' -> forall N, red1 (Abs N M) (Abs N M')
    | app_red_l :
        forall M1 N1, red1 M1 N1 -> forall M2, red1 (App M1 M2) (App N1 M2)
    | app_red_r :
        forall M2 N2, red1 M2 N2 -> forall M1, red1 (App M1 M2) (App M1 N2)
    | pair_red_T :
        forall T S, red1 T S -> forall M1 M2, red1 (Pair T M1 M2) (Pair S M1 M2)
    | pair_red_l :
        forall M1 N1, red1 M1 N1 -> forall T M2, red1 (Pair T M1 M2) (Pair T N1 M2)
    | pair_red_r :
        forall M2 N2, red1 M2 N2 -> forall T M1, red1 (Pair T M1 M2) (Pair T M1 N2)
    | prod_red_l :
        forall M1 N1, red1 M1 N1 -> forall M2, red1 (Prod M1 M2) (Prod N1 M2)
    | prod_red_r :
        forall M2 N2, red1 M2 N2 -> forall M1, red1 (Prod M1 M2) (Prod M1 N2)
    | sum_red_l :
        forall M1 N1, red1 M1 N1 -> forall M2, red1 (Sum M1 M2) (Sum N1 M2)
    | sum_red_r :
        forall M2 N2, red1 M2 N2 -> forall M1, red1 (Sum M1 M2) (Sum M1 N2)
    | subset_red_l :
        forall M1 N1, red1 M1 N1 -> forall M2, red1 (Subset M1 M2) (Subset N1 M2)
    | subset_red_r :
        forall M2 N2, red1 M2 N2 -> forall M1, red1 (Subset M1 M2) (Subset M1 N2)
    | pi1_red :
        forall M N, red1 M N -> red1 (Pi1 M) (Pi1 N)
    | pi2_red :
        forall M N, red1 M N -> red1 (Pi2 M) (Pi2 N)
    | let_in_red_l :
        forall M1 N1, red1 M1 N1 -> forall M2, red1 (Let_in M1 M2) (Let_in N1 M2)
    | let_in_red_r :
        forall M2 N2, red1 M2 N2 -> forall M1, red1 (Let_in M1 M2) (Let_in M1 N2).
      
  Inductive red M : term -> Prop :=
    | refl_red : red M M
    | trans_red : forall (P : term) N, red M P -> red1 P N -> red M N.

  Inductive conv M : term -> Prop :=
    | refl_conv : conv M M
    | trans_conv_red : forall (P : term) N, conv M P -> red1 P N -> conv M N
    | trans_conv_exp : forall (P : term) N, conv M P -> red1 N P -> conv M N.

  Inductive par_red1 : term -> term -> Prop :=
    | par_beta :
        forall M M',
        par_red1 M M' ->
        forall N N',
        par_red1 N N' -> forall T, par_red1 (App (Abs T M) N) (subst N' M')
    | par_pi1 : forall T, forall M M', par_red1 M M' -> 
      forall N, par_red1 (Pi1 (Pair T M N)) M'
    | par_pi2 : forall T M, forall N N', par_red1 N N' -> 
      par_red1 (Pi2 (Pair T M N)) N'
    | sort_par_red : forall s, par_red1 (Srt s) (Srt s)
    | ref_par_red : forall n, par_red1 (Ref n) (Ref n)
    | abs_par_red :
        forall M M',
        par_red1 M M' ->
        forall T T', par_red1 T T' -> par_red1 (Abs T M) (Abs T' M')
    | app_par_red :
        forall M M',
        par_red1 M M' ->
        forall N N', par_red1 N N' -> par_red1 (App M N) (App M' N')
    | pair_par_red : forall T T', par_red1 T T' ->
        forall M M',
        par_red1 M M' ->
        forall N N', par_red1 N N' -> par_red1 (Pair T M N) (Pair T' M' N')
    | prod_par_red :
        forall M M',
        par_red1 M M' ->
        forall N N', par_red1 N N' -> par_red1 (Prod M N) (Prod M' N')
    | sum_par_red :
        forall M M',
        par_red1 M M' ->
        forall N N', par_red1 N N' -> par_red1 (Sum M N) (Sum M' N')
    | subset_par_red :
        forall M M',
        par_red1 M M' ->
        forall N N', par_red1 N N' -> par_red1 (Subset M N) (Subset M' N')
    | pi1_par_red :
        forall M M', par_red1 M M' -> par_red1 (Pi1 M) (Pi1 M')
    | pi2_par_red :
        forall M M', par_red1 M M' -> par_red1 (Pi2 M) (Pi2 M')
    | let_in_par_red :
        forall M M',
        par_red1 M M' ->
        forall N N', par_red1 N N' -> par_red1 (Let_in M N) (Let_in M' N').

  Definition par_red := clos_trans term par_red1.

End Beta_Reduction.


  Hint Resolve beta pi1 pi2 abs_red_l abs_red_r app_red_l app_red_r pair_red_T pair_red_l pair_red_r : coc.
  Hint Resolve prod_red_l prod_red_r sum_red_l sum_red_r subset_red_l subset_red_r pi1_red pi2_red let_in_red_l let_in_red_r : coc.
  Hint Resolve refl_red refl_conv: coc.
  Hint Resolve par_beta par_pi1 par_pi2 sort_par_red ref_par_red abs_par_red app_par_red pair_par_red
    prod_par_red sum_par_red subset_par_red pi1_par_red pi2_par_red let_in_par_red: coc.

  Hint Unfold par_red: coc.


Section Normalisation_Forte.

  Definition normal t : Prop := forall u, ~ red1 t u.

  Definition sn : term -> Prop := Acc (transp _ red1).

End Normalisation_Forte.

  Hint Unfold sn: coc.



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



  Lemma one_step_red : forall M N, red1 M N -> red M N.
intros.
apply trans_red with M; auto with coc core arith sets.
Qed.

  Hint Resolve one_step_red: coc.


  Lemma red1_red_ind :
   forall N (P : term -> Prop),
   P N ->
   (forall M (R : term), red1 M R -> red R N -> P R -> P M) ->
   forall M, red M N -> P M.
cut
 (forall M N,
  red M N ->
  forall P : term -> Prop,
  P N -> (forall M (R : term), red1 M R -> red R N -> P R -> P M) -> P M).
intros.
apply (H M N); auto with coc core arith sets.

simple induction 1; intros; auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply H4 with N0; auto with coc core arith sets.

intros.
apply H4 with R; auto with coc core arith sets.
apply trans_red with P; auto with coc core arith sets.
Qed.


  Lemma trans_red_red : forall M N (P : term), red M N -> red N P -> red M P.
intros.
generalize H0 M H.
simple induction 1; auto with coc core arith sets.
intros.
apply trans_red with P0; auto with coc core arith sets.
Qed.
 

  Lemma red_red_app :
   forall u u0 v v0, red u u0 -> red v v0 -> red (App u v) (App u0 v0).
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_red with (App u P); auto with coc core arith sets.

intros.
apply trans_red with (App P v0); auto with coc core arith sets.
Qed.

Lemma red_red_pair :
   forall T T0 u u0 v v0, red T T0 -> red u u0 -> red v v0 -> red (Pair T u v) (Pair T0 u0 v0).
simple induction 1.
simple induction 1.
simple induction 1 ; intros ; auto with coc core arith sets.
apply trans_red with (Pair T u P); auto with coc core arith sets.

induction 4 ; intros ; auto with coc core arith sets.
apply trans_red with (Pair T P v); auto with coc core arith sets.
apply trans_red with (Pair T P N0); auto with coc core arith sets.
apply H2 ; auto with coc core arith sets.
apply trans_red with P0 ; auto.

induction 4.
induction 1 ; intros ; auto with coc core arith sets.
apply trans_red with (Pair P u v); auto with coc core arith sets.
apply trans_red with (Pair P u N0); auto with coc core arith sets.
apply H1 ; auto with coc core arith sets.
apply trans_red with P0; auto with coc core arith sets.

induction 1 ; intros ; auto with coc core arith sets.
apply trans_red with (Pair P N0 v); auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply trans_red with P0; auto with coc core arith sets.
apply trans_red with (Pair P N0 N1); auto with coc core arith sets.
apply H1 ; auto with coc core arith sets.
apply trans_red with P0; auto with coc core arith sets.
apply trans_red with P1; auto with coc core arith sets.
Qed.

Ltac red_red_tac t :=
  intros u ; elim u ; 
  [ (intros u0 ; elim u0; intros v v0 P; auto with coc core arith sets ;
     apply trans_red with (t u P); auto with coc core arith sets) 
  | intros v v0 P ; apply trans_red with (t P v0); auto with coc core arith sets ].

Lemma red_red_abs :
   forall u u0 v v0, red u u0 -> red v v0 -> red (Abs u v) (Abs u0 v0).
Proof.
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_red with (Abs u P); auto with coc core arith sets.

intros.
apply trans_red with (Abs P v0); auto with coc core arith sets.
Qed.


  Lemma red_red_prod :
   forall u u0 v v0, red u u0 -> red v v0 -> red (Prod u v) (Prod u0 v0).
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_red with (Prod u P); auto with coc core arith sets.

intros.
apply trans_red with (Prod P v0); auto with coc core arith sets.
Qed.

  Lemma red_red_sum :
   forall u u0 v v0, red u u0 -> red v v0 -> red (Sum u v) (Sum u0 v0).
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_red with (Sum u P); auto with coc core arith sets.

intros.
apply trans_red with (Sum P v0); auto with coc core arith sets.
Qed.

  Lemma red_red_subset :
   forall u u0 v v0, red u u0 -> red v v0 -> red (Subset u v) (Subset u0 v0).
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_red with (Subset u P); auto with coc core arith sets.

intros.
apply trans_red with (Subset P v0); auto with coc core arith sets.
Qed.

  Lemma red_red_pi1 : forall u u0, red u u0 -> red (Pi1 u) (Pi1 u0).
simple induction 1 ; auto with coc core arith sets.
intros.
apply trans_red with (Pi1 P); auto with coc core arith sets.
Qed.

  Lemma red_red_pi2 : forall u u0, red u u0 -> red (Pi2 u) (Pi2 u0).
simple induction 1 ; auto with coc core arith sets.
intros.
apply trans_red with (Pi2 P); auto with coc core arith sets.
Qed.

  Lemma red_red_let_in :
   forall u u0 v v0, red u u0 -> red v v0 -> red (Let_in u v) (Let_in u0 v0).
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_red with (Let_in u P); auto with coc core arith sets.

intros.
apply trans_red with (Let_in P v0); auto with coc core arith sets.
Qed.

  Hint Resolve red_red_app red_red_abs red_red_prod: coc.
  Hint Resolve red_red_pair red_red_sum red_red_subset red_red_let_in red_red_pi1 red_red_pi2 : coc.


  Lemma red1_lift :
   forall u v, red1 u v -> forall n k, red1 (lift_rec n u k) (lift_rec n v k).
simple induction 1; simpl in |- *; intros; auto with coc core arith sets.
rewrite distr_lift_subst; auto with coc core arith sets.
Qed.

  Hint Resolve red1_lift: coc.


  Lemma red1_subst_r :
   forall t u,
   red1 t u -> forall (a : term) k, red1 (subst_rec a t k) (subst_rec a u k).
simple induction 1; simpl in |- *; intros; auto with coc core arith sets.
rewrite distr_subst; auto with coc core arith sets.
Qed.


  Lemma red1_subst_l :
   forall (a : term) t u k,
   red1 t u -> red (subst_rec t a k) (subst_rec u a k).
simple induction a; simpl in |- *; auto with coc core arith sets.
intros.
elim (lt_eq_lt_dec k n);
 [ intro a0 | intro b; auto with coc core arith sets ].
elim a0; auto with coc core arith sets.
unfold lift in |- *; auto with coc core arith sets.
Qed.

  Hint Resolve red1_subst_l red1_subst_r: coc.


  Lemma red_prod_prod :
   forall u v t,
   red (Prod u v) t ->
   forall P : Prop,
   (forall a b : term, t = Prod a b -> red u a -> red v b -> P) -> P.
simple induction 1; intros.
apply H0 with u v; auto with coc core arith sets.

apply H1; intros.
inversion_clear H4 in H2.
inversion H2.
apply H3 with N1 b; auto with coc core arith sets.
apply trans_red with a; auto with coc core arith sets.

apply H3 with a N2; auto with coc core arith sets.
apply trans_red with b; auto with coc core arith sets.
Qed.


  Lemma red_sum_sum :
   forall u v t,
   red (Sum u v) t ->
   forall P : Prop,
   (forall a b : term, t = Sum a b -> red u a -> red v b -> P) -> P.
simple induction 1; intros.
apply H0 with u v; auto with coc core arith sets.

apply H1; intros.
inversion_clear H4 in H2.
inversion H2.
apply H3 with N1 b; auto with coc core arith sets.
apply trans_red with a; auto with coc core arith sets.

apply H3 with a N2; auto with coc core arith sets.
apply trans_red with b; auto with coc core arith sets.
Qed.

  Lemma red_subset_subset :
   forall u v t,
   red (Subset u v) t ->
   forall P : Prop,
   (forall a b : term, t = Subset a b -> red u a -> red v b -> P) -> P.
simple induction 1; intros.
apply H0 with u v; auto with coc core arith sets.

apply H1; intros.
inversion_clear H4 in H2.
inversion H2.
apply H3 with N1 b; auto with coc core arith sets.
apply trans_red with a; auto with coc core arith sets.

apply H3 with a N2; auto with coc core arith sets.
apply trans_red with b; auto with coc core arith sets.
Qed.

  Lemma red_sort_sort : forall s t, red (Srt s) t -> t <> Srt s -> False.
simple induction 1; intros; auto with coc core arith sets.
apply H1.
generalize H2.
case P; intros; try discriminate.
inversion_clear H4.
Qed.



  Lemma one_step_conv_exp : forall M N, red1 M N -> conv N M.
intros.
apply trans_conv_exp with N; auto with coc core arith sets.
Qed.


  Lemma red_conv : forall M N, red M N -> conv M N.
simple induction 1; auto with coc core arith sets.
intros; apply trans_conv_red with P; auto with coc core arith sets.
Qed.

  Hint Resolve one_step_conv_exp red_conv: coc.


  Lemma sym_conv : forall M N, conv M N -> conv N M.
simple induction 1; auto with coc core arith sets.
simple induction 2; intros; auto with coc core arith sets.
apply trans_conv_red with P0; auto with coc core arith sets.

apply trans_conv_exp with P0; auto with coc core arith sets.

simple induction 2; intros; auto with coc core arith sets.
apply trans_conv_red with P0; auto with coc core arith sets.

apply trans_conv_exp with P0; auto with coc core arith sets.
Qed.

  Hint Immediate sym_conv: coc.


  Lemma trans_conv_conv :
   forall M N (P : term), conv M N -> conv N P -> conv M P.
intros.
generalize M H; elim H0; intros; auto with coc core arith sets.
apply trans_conv_red with P0; auto with coc core arith sets.

apply trans_conv_exp with P0; auto with coc core arith sets.
Qed.


  Lemma conv_conv_prod :
   forall a b c d : term, conv a b -> conv c d -> conv (Prod a c) (Prod b d).
intros.
apply trans_conv_conv with (Prod a d).
elim H0; intros; auto with coc core arith sets.
apply trans_conv_red with (Prod a P); auto with coc core arith sets.

apply trans_conv_exp with (Prod a P); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_red with (Prod P d); auto with coc core arith sets.

apply trans_conv_exp with (Prod P d); auto with coc core arith sets.
Qed.


Lemma conv_conv_sum : forall a b c d : term, conv a b -> conv c d -> conv (Sum a c) (Sum b d).
Proof.
intros.
apply trans_conv_conv with (Sum a d).
elim H0; intros; auto with coc core arith sets.
apply trans_conv_red with (Sum a P); auto with coc core arith sets.

apply trans_conv_exp with (Sum a P); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_red with (Sum P d); auto with coc core arith sets.

apply trans_conv_exp with (Sum P d); auto with coc core arith sets.
Qed.


Lemma conv_conv_subset : 
  forall a b c d : term, conv a b -> conv c d -> conv (Subset a c) (Subset b d).
Proof.
intros.
apply trans_conv_conv with (Subset a d).
elim H0; intros; auto with coc core arith sets.
apply trans_conv_red with (Subset a P); auto with coc core arith sets.

apply trans_conv_exp with (Subset a P); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_red with (Subset P d); auto with coc core arith sets.

apply trans_conv_exp with (Subset P d); auto with coc core arith sets.
Qed.

Lemma conv_conv_pair : forall T S a b c d : term, conv T S -> conv a b -> conv c d -> conv (Pair T a c) (Pair S b d).
Proof.
intros.
apply trans_conv_conv with (Pair S b d).
elim H0; intros; auto with coc core arith sets.
apply trans_conv_red with (Pair a P); auto with coc core arith sets.

apply trans_conv_exp with (Pair a P); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_red with (Pair P d); auto with coc core arith sets.

apply trans_conv_exp with (Pair P d); auto with coc core arith sets.
Qed.


  Lemma conv_conv_lift :
   forall (a b : term) n k,
   conv a b -> conv (lift_rec n a k) (lift_rec n b k).
intros.
elim H; intros; auto with coc core arith sets.
apply trans_conv_red with (lift_rec n P k); auto with coc core arith sets.

apply trans_conv_exp with (lift_rec n P k); auto with coc core arith sets.
Qed.
 

  Lemma conv_conv_subst :
   forall (a b c d : term) k,
   conv a b -> conv c d -> conv (subst_rec a c k) (subst_rec b d k).
intros.
apply trans_conv_conv with (subst_rec a d k).
elim H0; intros; auto with coc core arith sets.
apply trans_conv_red with (subst_rec a P k); auto with coc core arith sets.

apply trans_conv_exp with (subst_rec a P k); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_conv with (subst_rec P d k); auto with coc core arith sets.

apply trans_conv_conv with (subst_rec P d k); auto with coc core arith sets.
apply sym_conv; auto with coc core arith sets.
Qed.

  Hint Resolve conv_conv_prod conv_conv_lift conv_conv_subst: coc.


  Lemma refl_par_red1 : forall M, par_red1 M M.
simple induction M; auto with coc core arith sets.
Qed.

  Hint Resolve refl_par_red1: coc.


  Lemma red1_par_red1 : forall M N, red1 M N -> par_red1 M N.
simple induction 1; auto with coc core arith sets; intros.
Qed.

  Hint Resolve red1_par_red1: coc.


  Lemma red_par_red : forall M N, red M N -> par_red M N.
red in |- *; simple induction 1; intros; auto with coc core arith sets.
apply t_trans with P; auto with coc core arith sets.
Qed.


  Lemma par_red_red : forall M N, par_red M N -> red M N.
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_red with (App (Abs T M') N'); auto with coc core arith sets.
apply trans_red with (Pi1 (Pair M' N0)); auto with coc core arith sets.
apply trans_red with (Pi2 (Pair M0 N')); auto with coc core arith sets.

intros.
apply trans_red_red with y; auto with coc core arith sets.
Qed.

  Hint Resolve red_par_red par_red_red: coc.


  Lemma par_red1_lift :
   forall n (a b : term),
   par_red1 a b -> forall k, par_red1 (lift_rec n a k) (lift_rec n b k).
simple induction 1; simpl in |- *; auto with coc core arith sets.
intros.
rewrite distr_lift_subst; auto with coc core arith sets.
Qed.


  Lemma par_red1_subst :
   forall c d : term,
   par_red1 c d ->
   forall a b : term,
   par_red1 a b -> forall k, par_red1 (subst_rec a c k) (subst_rec b d k).
simple induction 1; simpl in |- *; auto with coc core arith sets; intros.
rewrite distr_subst; auto with coc core arith sets.

elim (lt_eq_lt_dec k n); auto with coc core arith sets; intro a0.
elim a0; intros; auto with coc core arith sets.
unfold lift in |- *.
apply par_red1_lift; auto with coc core arith sets.
Qed.


  Lemma inv_par_red_abs :
   forall (P : Prop) T (U x : term),
   par_red1 (Abs T U) x ->
   (forall T' (U' : term), x = Abs T' U' -> par_red1 U U' -> P) -> P.
do 5 intro.
inversion_clear H; intros.
apply H with T' M'; auto with coc core arith sets.
Qed.

  Hint Resolve par_red1_lift par_red1_subst: coc.



  Lemma subterm_abs : forall t (m : term), subterm m (Abs t m).
intros.
apply Sbtrm_bind with t; auto with coc core arith sets.
Qed.

  Lemma subterm_prod : forall t (m : term), subterm m (Prod t m).
intros.
apply Sbtrm_bind with t; auto with coc core arith sets.
Qed.

  Lemma subterm_sum : forall t (m : term), subterm m (Sum t m).
intros.
apply Sbtrm_bind with t; auto with coc core arith sets.
Qed.

  Lemma subterm_subset : forall t (m : term), subterm m (Subset t m).
intros.
apply Sbtrm_bind with t; auto with coc core arith sets.
Qed.

  Lemma subterm_let_in : forall t (m : term), subterm m (Let_in t m).
intros.
apply Sbtrm_bind with t; auto with coc core arith sets.
Qed.

Hint Resolve subterm_abs subterm_prod subterm_sum subterm_subset
  subterm_let_in : coc.


(*
  Lemma mem_sort_ref: (s:sort)(n:nat)~(mem_sort s (Ref n)).
(Red; Intros).
Cut (b:term)(mem_sort s b)->b=(Ref n)->False.
Intros.
(Apply H0 with (Ref n); Auto with coc core arith sets).

Do 2 Intro.
(Elim H0 using clos_refl_trans_ind_left; Intros; Auto with coc core arith sets).
Discriminate H1.

Rewrite H4 in H3.
(Inversion_clear H3; Inversion_clear H5).
Save.
*)

  Lemma mem_sort_lift :
   forall t n k s, mem_sort s (lift_rec n t k) -> mem_sort s t.
simple induction t; simpl in |- *; intros; auto with coc core arith sets.
generalize H; elim (le_gt_dec k n); intros; auto with coc core arith sets.
inversion_clear H0.

inversion_clear H1.
apply mem_abs_l; apply H with n k; auto with coc core arith sets.

apply mem_abs_r; apply H0 with n (S k); auto with coc core arith sets.

inversion_clear H1.
apply mem_app_l; apply H with n k; auto with coc core arith sets.

apply mem_app_r; apply H0 with n k; auto with coc core arith sets.

inversion_clear H1.
apply mem_pair_l ; apply H with n k; auto with coc core arith sets.
apply mem_pair_r ; apply H0 with n k; auto with coc core arith sets.

inversion_clear H1.
apply mem_prod_l; apply H with n k; auto with coc core arith sets.

apply mem_prod_r; apply H0 with n (S k); auto with coc core arith sets.

inversion_clear H1.
apply mem_sum_l; apply H with n k; auto with coc core arith sets.

apply mem_sum_r; apply H0 with n (S k); auto with coc core arith sets.

inversion_clear H1.
apply mem_subset_l; apply H with n k; auto with coc core arith sets.

apply mem_subset_r; apply H0 with n (S k); auto with coc core arith sets.

inversion_clear H0.
apply mem_pi1 ; apply H with n k; auto with coc core arith sets.

inversion_clear H0.
apply mem_pi2 ; apply H with n k; auto with coc core arith sets.

inversion_clear H1.
apply mem_let_in_l; apply H with n k; auto with coc core arith sets.

apply mem_let_in_r; apply H0 with n (S k); auto with coc core arith sets.

Qed.


  Lemma mem_sort_subst :
   forall (b a : term) n s,
   mem_sort s (subst_rec a b n) -> mem_sort s a \/ mem_sort s b.
simple induction b; simpl in |- *; intros; auto with coc core arith sets.

generalize H; elim (lt_eq_lt_dec n0 n); [ intro a0 | intro b0 ].
elim a0; intros.
inversion_clear H0.

left.
apply mem_sort_lift with n0 0; auto with coc core arith sets.

intros.
inversion_clear H0.

 try (inversion_clear H1 ; [
    elim H with a n s; auto with coc core arith sets |
    elim H0 with a (S n) s; intros; auto with coc core arith sets]).


 try (inversion_clear H1 ; [
    elim H with a n s; auto with coc core arith sets |
    elim H0 with a n s; intros; auto with coc core arith sets]).

 try (inversion_clear H1 ; [
    elim H with a n s; auto with coc core arith sets |
    elim H0 with a n s; intros; auto with coc core arith sets]).

inversion_clear H1 ; [
elim H with a n s; auto with coc core arith sets |
elim H0 with a (S n) s; intros; auto with coc core arith sets].

inversion_clear H1 ; [
elim H with a n s; auto with coc core arith sets |
elim H0 with a (S n) s; intros; auto with coc core arith sets].
inversion_clear H1 ; [
elim H with a n s; auto with coc core arith sets |
elim H0 with a (S n) s; intros; auto with coc core arith sets].
inversion_clear H0.
elim (H _ _ _ H1) ; intros ; auto with coc core arith sets.
inversion_clear H0.
elim (H _ _ _ H1) ; intros ; auto with coc core arith sets.
inversion_clear H1 ; [
elim H with a n s; auto with coc core arith sets |
elim H0 with a (S n) s; intros; auto with coc core arith sets].
Qed.

  Lemma red_sort_mem : forall t s, red t (Srt s) -> mem_sort s t.
intros.
pattern t in |- *.
apply red1_red_ind with (Srt s); auto with coc core arith sets.
do 4 intro.
elim H0; intros ; try (inversion_clear H4; auto with coc core arith sets).
elim mem_sort_subst with M0 N 0 s; intros; auto with coc core arith sets.
apply mem_pi1 ; auto with coc core arith sets.
apply mem_pi2 ; auto with coc core arith sets.
Qed.

  Lemma red_normal : forall u v, red u v -> normal u -> u = v.
simple induction 1; auto with coc core arith sets; intros.
absurd (red1 u N); auto with coc core arith sets.
absurd (red1 P N); auto with coc core arith sets.
elim (H1 H3).
unfold not in |- *; intro; apply (H3 N); auto with coc core arith sets.
Qed.



  Lemma sn_red_sn : forall a b : term, sn a -> red a b -> sn b.
unfold sn in |- *.
simple induction 2; intros; auto with coc core arith sets.
apply Acc_inv with P; auto with coc core arith sets.
Qed.


  Lemma commut_red1_subterm : commut _ subterm (transp _ red1).
red in |- *.
simple induction 1; intros.
inversion_clear H0.
exists (Abs t z); auto with coc core arith sets.

exists (Prod t z); auto with coc core arith sets.

exists (Sum t z); auto with coc core arith sets.

exists (Subset t z); auto with coc core arith sets.

exists (Let_in t z); auto with coc core arith sets.

inversion_clear H0.
exists (Abs z n); auto with coc core arith sets.

exists (App z v); auto with coc core arith sets.

exists (App u z); auto with coc core arith sets.

exists (Pair z v); auto with coc core arith sets.
exists (Pair u z); auto with coc core arith sets.

exists (Prod z n); auto with coc core arith sets.
exists (Sum z n); auto with coc core arith sets.
exists (Subset z n); auto with coc core arith sets.
exists (Pi1 z); auto with coc core arith sets.
exists (Pi2 z); auto with coc core arith sets.
exists (Let_in z n); auto with coc core arith sets.
Qed.


 Lemma subterm_sn :
   forall a : term, sn a -> forall b : term, subterm b a -> sn b.
unfold sn in |- *.
simple induction 1; intros.
apply Acc_intro; intros.
elim commut_red1_subterm with x b y; intros; auto with coc core arith sets.
apply H1 with x0; auto with coc core arith sets.
Qed.


  Lemma sn_prod : forall A, sn A -> forall B, sn B -> sn (Prod A B).
unfold sn in |- *.
simple induction 1.
simple induction 3; intros.
apply Acc_intro; intros.
inversion_clear H5; auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply Acc_intro; auto with coc core arith sets.
Qed.

  Lemma sn_sum : forall A, sn A -> forall B, sn B -> sn (Sum A B).
unfold sn in |- *.
simple induction 1.
simple induction 3; intros.
apply Acc_intro; intros.
inversion_clear H5; auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply Acc_intro; auto with coc core arith sets.
Qed.

  Lemma sn_pair : forall A, sn A -> forall B, sn B -> sn (Pair A B).
unfold sn in |- *.
simple induction 1.
simple induction 3; intros.
apply Acc_intro; intros.
inversion_clear H5; auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply Acc_intro; auto with coc core arith sets.
Qed.

  Lemma sn_subset : forall A, sn A -> forall B, sn B -> sn (Subset A B).
unfold sn in |- *.
simple induction 1.
simple induction 3; intros.
apply Acc_intro; intros.
inversion_clear H5; auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply Acc_intro; auto with coc core arith sets.
Qed.

  Lemma sn_let_in : forall A, sn A -> forall B, sn B -> sn (Let_in A B).
unfold sn in |- *.
simple induction 1.
simple induction 3; intros.
apply Acc_intro; intros.
inversion_clear H5; auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply Acc_intro; auto with coc core arith sets.
Qed.


  Lemma sn_subst : forall T M, sn (subst T M) -> sn M.
intros.
cut (forall t, sn t -> forall m : term, t = subst T m -> sn m).
intros.
apply H0 with (subst T M); auto with coc core arith sets.

unfold sn in |- *.
simple induction 1; intros.
apply Acc_intro; intros.
apply H2 with (subst T y); auto with coc core arith sets.
rewrite H3.
unfold subst in |- *; auto with coc core arith sets.
Qed.