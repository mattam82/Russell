Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Basic.
Require Import Lambda.TPOSR.Thinning.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.Coercion.
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.ChurchRosser.
Require Import Lambda.TPOSR.CoerceDepth.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.

Require Import Omega.
Require Import Coq.Arith.Max.

Lemma depth_prod_prod_l :  forall n0 n1 n2 n3, 
 n3 + n2 < S (max n2 n1 + S (max n3 n0)).
Proof.
  intros.
  rewrite max_SS.
  pose (le_max_l (S n3) (S n0)).
  pose (le_max_r (S n3) (S n0)).
  pose (le_max_l n2 n1).
  pose (le_max_r n2 n1).
  omega.
Qed.

Lemma depth_prod_prod_r : forall n0 n1 n2 n3, n3 + n1 < S (max n0 n3 + S (max n2 n1)).
Proof.
  intros.
  rewrite max_SS.
  pose (le_max_l (S n2) (S n1)).
  pose (le_max_r (S n2) (S n1)).
  pose (le_max_l n0 n3).
  pose (le_max_r n0 n3).
  omega.
Qed.

Lemma depth_prod_conv_prod : 
  forall n0 n1 n2 n3, n3 + S n2 < S (max n2 n1 + S (S (max n3 n0))).
Proof.
  intros.
  rewrite max_SS.
  pose (le_max_l (S n3) (S n0)).
  pose (le_max_r (S n3) (S n0)).
  pose (le_max_l n2 n1).
  pose (le_max_r n2 n1).
  omega.
Qed.

Lemma depth_prod_conv_prod2 : forall n0 n1 n2 n3, n1 + S n0 < S (max n2 n1 + S (S (max n3 n0))).
Proof.
  intros.
  rewrite max_SS.
  pose (le_max_l (S n3) (S n0)).
  pose (le_max_r (S n3) (S n0)).
  pose (le_max_l n2 n1).
  pose (le_max_r n2 n1).
  omega.
Qed.

Lemma depth_sum_conv_sum : forall n0 n1 n2 n3, S (n3 + n2) < S (max n2 n1 + S (S (max n3 n0))).
Proof.
   intros.
   rewrite max_SS.
   pose (le_max_l (S n3) (S n0)).
  pose (le_max_r (S n3) (S n0)).
  pose (le_max_l n2 n1).
  pose (le_max_r n2 n1).
  omega.
Qed.

Lemma depth_sum_conv_sum2 : forall n0 n1 n2 n3, n3 + S n2 < S (max n3 n1 + S (S (max n2 n0))).
Proof.
   intros.
   rewrite max_SS.
   pose (le_max_l (S n2) (S n0)).
  pose (le_max_r (S n2) (S n0)).
  pose (le_max_l n3 n1).
  pose (le_max_r n3 n1).
  omega.
Qed.

Lemma depth_conv_prod : forall n0 n1 n2 n3, S (n3 + n2) < S (S (max n2 n1 + (S (max n3 n0)))).
Proof.
   intros.
   rewrite max_SS.
   pose (le_max_l (S n3) (S n0)).
  pose (le_max_r (S n3) (S n0)).
  pose (le_max_l n2 n1).
  pose (le_max_r n2 n1).
  omega.
Qed.

Lemma depth_conv_prod2 : forall n0 n1 n2 n3, S (n1 + n3) < S (S (max n2 n1 + S (max n0 n3))).
Proof.
   intros.
   rewrite max_SS.
   pose (le_max_l (S n0) (S n3)).
  pose (le_max_r (S n0) (S n3)).
  pose (le_max_l n2 n1).
  pose (le_max_r n2 n1).
  omega.
Qed.
Lemma depth_conv_sum : forall n0 n1 n2 n3, S (n3 + n2) < S (S (max n3 n0 + S (max n2 n1))).
Proof.
   intros.
   rewrite max_SS.
   pose (le_max_l (S n2) (S n1)).
  pose (le_max_r (S n2) (S n1)).
  pose (le_max_l n3 n0).
  pose (le_max_r n3 n0).
  omega.
Qed.

Lemma depth_conv_sum2 : forall n0 n1 n2 n3, n3 + S n2 < S (S (max n1 n3 + S (max n0 n2))).
Proof.
   intros.
   rewrite max_SS.
   pose (le_max_l (S n0) (S n2)).
  pose (le_max_r (S n0) (S n2)).
  pose (le_max_l n1 n3).
  pose (le_max_r n1 n3).
  omega.
Qed.

Lemma coerces_sort_l : forall e T U s n, e |-- T >>> U : s [n] -> e |-- T -> T : s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc core.
  apply tposr_prod with s ; auto with coc.
  apply tposr_sum with s s' ; auto with coc.
Qed.

Lemma coerces_sort_r : forall e T U s n, e |-- T >>> U : s [n] -> e |-- U -> U : s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc core.
  apply tposr_prod with s ; auto with coc.
  apply tposr_sum with s s' ; auto with coc.
Qed.

Theorem coerce_trans_aux : forall n : nat,
(forall e A B s m, forall d1 : e |-- A >>> B : s [m], 
forall C p, forall d2 : e |-- B >>> C : s [p],
  n = m + p ->
  exists q, e |-- A >>> C : s [q]).
Proof.
  intros n.
  pattern n.
  apply (wf_lt_induction_type).

  intros x IH.
  simple induction 1 ;  auto with coc.
  intros.
  exists p ; auto.

  clear e A B s m d1.
  intros ; clear H0 H4.
  set(dleft := S (max n0 m)).
  assert(Hleft:e |-- Prod_l A B >>> Prod_l A' B' : s' [S (max n0 m)]).
  apply coerces_prod with s ; auto with coc.

    apply (coerces_db_dep
  ( fun e1 T0 C0 s0 p0 => fun _ : (e1 |-- T0 >>> C0 : s0 [p0]) =>
   e1 = e -> T0 = Prod_l A' B' -> C0 = C -> s0 = s' -> p0 = p ->
   exists q, e1 |-- Prod_l A B >>> C0 : s' [q])) 
   with (Prod_l A' B') s' p ; intros ; subst ; auto with coc ; try discriminate.
  simpl in IH.

  (* prod, refl *)
  exists (S (max n0 m)).
  apply coerces_prod with s ; auto with coc.
  
  (* prod, prod *)
  clear H0 ; clear H4.
  inversion H9 ; subst.
  assert(eq:=unique_sort t0 H1).
  rewrite eq in c.
  rewrite eq in t0.
  rewrite eq in t.
  clear s0 eq.
  
  assert(exists q, e |-- A'0 >>> A : s [q]).
  apply (IH (n1 + n0)) with A' n1 n0 ; auto.
  simpl.
  apply depth_prod_prod_l.
  destruct_exists.

  assert(exists q, A'0 :: e |-- B >>> B'0 : s' [q]) ; destruct_exists.
  assert(coerce_in_env (A' :: e) (A'0 :: e)) ; intros.
  apply coerce_env_hd with s n1 ; auto with coc.
  assert(tposr_wf (A'0 :: e)).
  apply wf_cons with A'0 s ; auto with coc.
  pose (coerce_conv_env H3 H4 H7).
  apply IH with (m + m0) B' m m0 ; auto with coc.
  simpl.
  apply depth_prod_prod_r.
    
  exists (S (max x x0)).
  apply coerces_prod with s ; auto with coc.

  (* prod, subset *)
  clear H0.
  assert(exists q, e |-- Prod_l A B >>> U' : set [q]) ; destruct_exists.
  apply IH with (S (max n0 m) + n1) (Prod_l A' B') (S (max n0 m)) n1 ; auto with coc.
  simpl.
  omega.
  exists (S x) ; apply coerces_sub_r ; auto with coc.

  (* prod, conv_l *)
  clear H0.

  assert(e |-- Prod_l A B -> Prod_l A B : s').
  apply tposr_prod with s ; auto with coc.
  assert(e |-- Prod_l A' B' -> Prod_l A' B' : s').
  apply tposr_prod with s ; auto with coc.

  destruct c.

  (* prod, conv_l < refl *) 
  exists (S (S (max n0 m))).
  apply coerces_conv_r with (Prod_l A' B') ; auto with coc.

  (* prod, conv_l < prod *)
  destruct (injectivity_of_pi t2) ; destruct_exists.
  rewrite <- (unique_sort H8 (eq_refl_r H11)) in H11 ; clear x.
  
  rewrite <- e1 in H1.
  pose (unique_sort H1 t).
  generalize dependent A'0.
  rewrite e2.
  intros.

  assert(HA1A' : e |-- A' ~= A1 : s).
  destruct (inv_eq_prod_l_set c2).
  pose(coerces_conv_l).
  rewrite e2 in t7.
  rewrite (unique_sort (eq_refl_r t10) t11) in t10.
  assumption.

  assert(e |-- A'0 >>> A : s).
  rewrite e2 in t7.
  set (d := coerces_conv_l t10 t t0 (tposr_eq_sym HA1A') c).
  apply (IH (depth c1_1 + depth d)) with A1 c1_1 d ; auto with coc.
  simpl.
  rewrite H4 ; simpl.
  apply depth_prod_conv_prod.
  
  apply coerces_prod with s ; auto with coc core.

  cut(coerce_in_env (A' :: e) (A'0 :: e)) ; intros.
  assert(tposr_wf (A'0 :: e)).
  apply wf_cons with A'0 s ; auto with coc.

  cut(A'0 :: e |-- B' -> B' : s') ; intros.
  cut(A'0 :: e |-- B0 -> B0 : s') ; intros.
  pose (inv_eq_prod_r_set c2).
  assert(A'0 :: e |-- B' ~= B0 : s').
  apply eq_conv_env with (A1 :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  set (d := coerces_conv_l H7 H8 t9 H9 c1_2).
  destruct (coerce_conv_env c0 H5 H6).
  apply (IH (depth c0 + depth d)) with B' x1 d ; auto with coc.
  simpl.
  rewrite H4.
  apply depth_prod_conv_prod2.

  apply (coerces_sort_l c1_2).
  apply (typ_conv_env t2 H5 H6).
  apply coerce_env_hd with s ; auto with coc core.
  apply coerces_conv_r with A1 ; auto with coc core.
  rewrite e2 in t7.
  apply t10.

  (* prod, conv_l < sum *)
  elim conv_prod_sum with A' B' A1 B0 ; auto with coc.
  apply (tposr_eq_conv c2).

  (* prod, conv_l < sub_l *)
  elim conv_prod_subset with A' B' U P ; auto with coc.
  apply (tposr_eq_conv c2).
  
  (* prod, conv_l < sub_r *)
  apply coerces_sub_r ; auto with coc core.
  pose (coerces_conv_l t3 t4 (coerces_sort_r c1) c2 c1).
  pose (coerces_prod c t t0 c0 t1 t2).
  apply (IH (depth c4 + depth c3)) with (Prod_l A' B') c4 c3 ; auto.
  simpl.
  rewrite H4.
  simpl.
  omega.

  (* prod, conv_l < conv_l *)
  assert(e |-- Prod_l A' B' ~= B0 : s1).
  apply tposr_eq_trans with A1 ; auto with coc.
  pose (coerces_conv_l t3 t7 t8 H1 c1).
  pose (coerces_prod c t t0 c0 t1 t2).
  apply (IH (depth c4 + depth c3)) with (Prod_l A' B') c4 c3.
  rewrite H4 ; simpl ; auto ; omega.
  auto.

  (* prod, conv_l < conv_r *)
  apply coerces_conv_r with B0 ; auto with coc.

  pose (coerces_prod c t t0 c0 t1 t2).
  pose (coerces_conv_l t3 t6 t7 c2 c1).
  apply (IH (depth c3 + depth c4)) with (Prod_l A' B') c3 c4.
  rewrite H4 ; simpl ; auto.
  omega.
  auto.

   (* prod, conv_r *)
   clear H.
  simpl in H4.
  rename t6 into c2.
  generalize dependent c1 ; generalize dependent c2.
  generalize dependent t3 ; generalize dependent t4 ; generalize dependent t5.
  rewrite H0.
  rewrite H1.
  rewrite H2.
  rewrite H3.
  clear H0 H1 H2 H3.
  intros.
  clear d2.

   apply coerces_conv_r with B0 ; auto with coc.
   apply tposr_prod with s ; auto with coc.

   pose (coerces_prod c t t0 c0 t1 t2).
   apply (IH (depth c3 + depth c1)) with (Prod_l A' B') c3 c1.
   rewrite H4.
   simpl.
   omega.
   auto.

 (* sum, _ *)
 clear e A B s d1; intros; clear H H0.
 generalize H1 ; clear H1.
 rename s0 into sum_sort0.
 rename s1 into sum_sort1.
   apply (coerces_db_dep (fun e1 T0 C0 s0 => fun d : (e1 |-- T0 >>> C0 : s0) =>
     e1 = e -> T0 = Sum_l A' B' -> C0 = C -> s0 = s'' ->     
     (x = depth (coerces_sum c t t0 c0 t1 t2 sum_sort0 sum_sort1) + depth d) ->
     e |-- Sum_l A B >>> C0 : s'')) ; intros ; auto with coc ; try discriminate.

  (* sum, refl *)
  rewrite H0 ;
  apply coerces_sum with s s' ; auto with coc.
  
  (* sum, sum *)
  clear H ; clear H0.
  simpl in H5.
  inversion H2.
  generalize dependent c1.
  generalize dependent t3 ; generalize dependent t4.
  generalize dependent c2 ; generalize dependent t5 ; generalize dependent t6.
  generalize dependent s1 ; generalize dependent s2.
  rewrite H1.
  clear H1.
  generalize dependent e.
  rewrite H0.
  rewrite H6.
  rewrite H4.
  intros.

  generalize dependent c1 ; generalize dependent t3 ; generalize dependent t4.
  intros t4.
  pose (unique_sort t t4).
  rewrite <- e1.
  intros.

  assert(e |-- A >>> A'0 : s).
  apply (IH (depth c1 + depth c)) with A' c c1 ; auto.
  rewrite H5 ; simpl ; auto with coc arith.
  apply depth_prod_prod_l.
  auto with arith.

  cut(coerce_in_env (A' :: e) (A :: e)) ; intros.
  assert(tposr_wf (A :: e)).
  apply wf_cons with A s ; auto with coc.
  destruct (coerce_conv_env c2 H1 H7).
  
  apply coerces_sum with s s' ; auto with coc.
  
  generalize dependent A.
  rewrite (unique_sort t2 t5).
  intros.
  apply (IH (depth c0 + depth x0)) with B' c0 x0 ; auto.
  rewrite e2.
  rewrite H5.
  simpl.
  apply depth_prod_prod_r.
  rewrite (unique_sort t2 t5) ; auto.
  apply coerce_env_hd with s ; auto with coc.

  (* sum, subset *)
  clear H.
  simpl in H4.
  rewrite <- H3 in sum_sort0.
  rewrite <- H2 in d2.
  pose (coerces_sort_r d2).
  rewrite <- H3.
  apply coerces_sub_r.
  generalize dependent c1.
  rewrite H1 ; rewrite H0.
  intros.
  generalize dependent e.
  rewrite <- H3.
  intros.
  rewrite <- H3 in sum_sort1.
  pose (coerces_sum c t t0 c0 t1 t2 sum_sort0 sum_sort1).
  set (dc2 := depth c2).
  apply (IH (depth c2 + depth c1)) with (Sum_l A' B') c2 c1 ; auto.
  rewrite H4.
  simpl.
  omega.
  
  rewrite <- H0 ; auto.

  (* sum, conv_l *)
  clear H.
  simpl in H4.
  rename t6 into c2.
  generalize dependent c1 ; generalize dependent c2.
  generalize dependent t3 ; generalize dependent t4 ; generalize dependent t5.
  rewrite H0.
  rewrite H1.
  rewrite H2.
  rewrite H3.
  clear H0 H1 H2 H3.
  intros.
  clear d2.

  assert(e |-- Sum_l A B -> Sum_l A B : s'').
  apply tposr_sum with s s' ; auto with coc.
  assert(e |-- Sum_l A' B' -> Sum_l A' B' : s'').
  apply tposr_sum with s s' ; auto with coc.
  assert(e |-- Sum_l A B >>> Sum_l A' B' : s'').
  apply coerces_sum with s s' ; auto with coc.
  
  destruct c1.

  (* sum, conv_l < refl *) 
  apply coerces_conv_r with (Sum_l A' B') ; auto with coc.

  (* sum, conv_l < prod *)
  elim conv_prod_sum with A1 B0 A' B'; auto with coc.
  pose (tposr_eq_conv c2) ; auto with coc.

  (* sum, conv_l < sum *)
  simpl in H4.
  induction (inv_conv_sum_sort_l_set t3 t4 c2).
  destruct p.
  pose (unique_sort t7 H3).
  pose (unique_sort H2 t).
  generalize dependent A'0.
  rewrite e1.
  rewrite e2.
  intros.

  assert(HA'A1:e |-- A' ~= A1 : s).
  destruct (inv_eq_sum_l_set c2).
  rewrite <- (unique_sort H3 (eq_refl_r t10)) in t10.
  rewrite e2 in t10.
  assumption.

  assert(e |-- A >>> A'0 : s).
  
  rewrite e2 in H3.
  set (d := coerces_conv_l t H5 t6 HA'A1 c1_1).
  apply (IH (depth c + depth d)) with A' c d ; auto with coc.
  simpl.
  rewrite H4 ; simpl.
  apply depth_sum_conv_sum2.

  induction (inv_conv_sum_sort_r_set t3 t4 c2).
  destruct p.
  pose (unique_sort t2 H6).
  assert(A' :: e |-- B0 -> B0 : s'0).
  apply typ_conv_env with (A1 :: e) ; auto with coc.
  apply coerce_env_hd with s ; intuition ; auto with coc.
  apply coerces_conv_l with A1 ; auto with coc.
  apply (eq_refl_r HA'A1).
  apply (eq_refl_r HA'A1).
  apply coerces_refl.
  apply (eq_refl_r HA'A1).
  apply wf_cons with A' s ; auto with coc.
  pose (unique_sort H7 H8).

  apply coerces_sum with s s' ; auto with coc core.

  cut(coerce_in_env (A1 :: e) (A :: e)) ; intros.
  assert(tposr_wf (A :: e)).
  apply wf_cons with A s ; auto with coc.
  
  generalize dependent B'.
  rewrite e4.
  intros.
  generalize dependent B'0.
  rewrite <- e3.
  intros.

  cut(A :: e |-- B' -> B' : s') ; intros.
  cut(A :: e |-- B0 -> B0 : s') ; intros.
  cut(A :: e |-- B'0 -> B'0 : s') ; intros.
  assert(A :: e |-- B' ~= B0 : s').
  destruct (inv_eq_sum_r_set c2).
  rewrite (unique_sort (eq_refl_l t10) t2) in t10.
  apply eq_conv_env with (A' :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  destruct (coerce_conv_env c1_2 H9 H10).
  set (d := coerces_conv_l H11 H12 H13 H14 x2).
  apply (IH (depth c0 + depth d)) with B' c0 d ; auto with coc.
  simpl.
  rewrite e5.
  rewrite H4.
  apply depth_prod_conv_prod2.

  apply typ_conv_env with (A'0 :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.

  apply typ_conv_env with (A1 :: e) ; auto with coc.
  apply (coerces_sort_l c1_2).
  apply (coerces_sort_r c0).

  apply coerce_env_hd with s ; auto with coc.
  apply coerces_conv_r with A' ; auto with coc core.
  rewrite <- e2 ; auto.
  rewrite e3.
  rewrite e4.
  assumption.

  (* sum, conv_l < sub_l *)
  elim conv_subset_sum with U P  A' B' ; auto with coc.
  pose (tposr_eq_conv c2) ; auto with coc.
 
  (* sum, conv_l < sub_r *)
  apply coerces_sub_r ; auto with coc core.
  pose (coerces_conv_l t3 t4 (coerces_sort_r c1) c2 c1).
  pose (coerces_sum c t t0 c0 t1 t2 sum_sort0 sum_sort1).
  apply (IH (depth c4 + depth c3)) with (Sum_l A' B') c4 c3 ; auto.
  simpl.
  rewrite H4.
  simpl.
  omega.

  (* sum, conv_l < conv_l *)
  assert(e |-- Sum_l A' B' ~= B0 : s1).
  apply tposr_eq_trans with A1 ; auto with coc.
  pose (coerces_conv_l t3 t7 t8 H2 c1).
  pose (coerces_sum c t t0 c0 t1 t2 sum_sort0 sum_sort1).
  apply (IH (depth c4 + depth c3)) with (Sum_l A' B') c4 c3.
  rewrite H4 ; simpl ; auto ; omega.
  auto.

  (* sum, conv_l < conv_r *)
  apply coerces_conv_r with B0 ; auto with coc.

  pose (coerces_sum c t t0 c0 t1 t2 (sum_sort0) sum_sort1).
  pose (coerces_conv_l t3 t6 t7 c2 c1).
  apply (IH (depth c3 + depth c4)) with (Sum_l A' B') c3 c4.
  rewrite H4 ; simpl ; auto.
  omega.
  auto.

   (* sum, conv_r *)
   clear H.
  simpl in H4.
  rename t6 into c2.
  generalize dependent c1 ; generalize dependent c2.
  generalize dependent t3 ; generalize dependent t4 ; generalize dependent t5.
  rewrite H0.
  rewrite H1.
  rewrite H2.
  rewrite H3.
  clear H0 H1 H2 H3.
  intros.
  clear d2.

   apply coerces_conv_r with B0 ; auto with coc.
   apply tposr_sum with s s' ; auto with coc.

   pose (coerces_sum c t t0 c0 t1 t2 sum_sort0 sum_sort1).
   apply (IH (depth c3 + depth c1)) with (Sum_l A' B') c3 c1.
   rewrite H4.
   simpl.
   omega.
   auto.

 (* sub_l *)
 intros.
 apply coerces_sub_l ; auto with coc.
 apply (IH (depth c + depth d2)) with U' c d2.
 rewrite H0.
 simpl.
 omega.
 auto.

 (* sub_r *)
 clear e A B s d1 ; intros.
 generalize H0 ; clear H0.

 apply (coerces_db_dep (fun e1 T0 C0 s0 => fun d : (e1 |-- T0 >>> C0 : s0) =>
   e1 = e -> T0 = Subset_l U' P -> C0 = C -> s0 = set ->     
   x = depth (coerces_sub_r c t) + depth d -> 
   e |-- U >>> C : set))  ; intros ; auto with coc ; try discriminate.

  (* sub_r, refl *)
  generalize dependent e.
  rewrite <- H2.
  clear H2.
  generalize dependent t0.
  rewrite H1.
  intros.
  apply (coerces_sub_r c t).
  
  (* sub_r, sub_l *)
  clear H0.
  simpl in H5.
  inversion H2.
  generalize dependent U0.
  rewrite H1.
  rewrite H3.
  rewrite H7.
  intros.
  generalize dependent c0.
  rewrite H6 .
  intros.
  apply (IH (depth c + depth c0)) with U' c c0.
  rewrite H5 ; simpl ; auto.
  omega.
  auto.

  (* sub_r, sub_r *)
  clear H0.
  simpl in H5.
  generalize dependent U'0.
  rewrite H1 ; rewrite H2 ;  intros.
  rewrite <- H3.
  
  pose (coerces_sub_r c t).
  apply coerces_sub_r ; auto with coc.
  apply (IH (depth c1 + depth c0)) with (Subset_l U' P) c1 c0.
  rewrite H5 ; simpl ; auto.
  omega.
  auto.

  (* sub_r, conv_l *)
  clear H0.
  simpl in H5.
  generalize dependent s.
  rewrite H1.
  rewrite H2.
  rewrite H3.
  intros.
  pose (HUset := coerces_sort_l c).
  pose (HU'set := coerces_sort_r c).

  clear d2.
  destruct c0.
  
  (* sub_r, conv_l < refl *)
  apply coerces_conv_r with (Subset_l U' P)  ; auto with coc.
  rewrite <- H4 ; auto.
  rewrite <- H4 ; auto.

  (* sub_r, conv_l < prod *)
  elim conv_prod_subset with A0 B U' P ; auto with coc.
  pose (tposr_eq_conv t3) ; auto with coc.

  (* sub_r, conv_l < sum *)
  elim conv_subset_sum with U' P A0 B ; auto with coc.
  pose (tposr_eq_conv t3) ; auto with coc.

  (* sub_r, conv_l < sub_l *)
  pose (inv_eq_subset_l_set t3).
  
  pose (coerces_conv_r (coerces_sort_l c) (coerces_sort_r c) (eq_refl_r t5) c t5).
  apply (IH (depth c1 + depth c0)) with U0 c1 c0.
  rewrite H5 ; simpl.
  omega.
  auto with arith.

  (* sub_r, conv_l < sub_r *)
  apply coerces_sub_r ; auto.
  pose (coerces_conv_l t0 t1 (coerces_sort_r c0) t3 c0).
  pose (coerces_sub_r c t).
  apply (IH (depth c2 + depth c1)) with (Subset_l U' P) c2 c1 ; auto.
  rewrite H5 ; simpl.
  omega.
  auto with arith.
  
  (* sub_r, conv_l < conv_l *)
  assert (e |-- Subset_l U' P ~= B : s).
  apply tposr_eq_trans with A0 ; auto with coc.
  pose (coerces_sub_r c t).
  pose (coerces_conv_l t0 t5 t6 H0 c0).
  generalize dependent e.
  rewrite H4.
  intros.
  apply (IH (depth c1 + depth c2)) with (Subset_l U' P) c1 c2 ; auto.
  rewrite H5 ; simpl.
  omega.

  (* sub_r, conv_l < conv_r *)
  generalize dependent e.
  rewrite H4.
  intros.
  apply coerces_conv_r with B ; auto with coc.
  pose (coerces_sub_r c t).
  pose (coerces_conv_l t0 t1 t5 t3 c0).
  apply (IH (depth c1 + depth c2)) with (Subset_l U' P) c1 c2 ; auto.
  rewrite H5 ; simpl.
  omega.

  (* sub_r, conv_r *)
  generalize dependent s.
  rewrite H1.
  intros.
  generalize dependent e.
  rewrite H2 ; rewrite H4.
  intros.
  rewrite <- H3.
  apply coerces_conv_r with B ; auto with coc.
  apply (coerces_sort_l c).
  pose (coerces_sub_r c t).
  apply (IH (depth c1 + depth c0)) with (Subset_l U' P) c1 c0 ; auto.
  rewrite H5 ; simpl.
  omega.

  (* conv_l *)
  intros.
  apply coerces_conv_l with B0 ; auto with coc.
  apply (coerces_sort_r d2).
  apply (IH (depth c + depth d2)) with C c d2.
  rewrite H0.
  simpl.
  omega.
  auto.
  
  (* conv_r *)
  clear e A B s d1.
  intros. clear H.
  simpl in H0.

  destruct d2 ; simpl in H0.

  (* conv_r, refl *)
  apply coerces_conv_r with B ; auto with coc.

  (* conv_r, prod *)
  assert(e |-- Prod_l A' B' -> Prod_l A' B' : s').
  apply tposr_prod with s ; auto with coc.
  destruct c ;
  pose (H1 := coerces_prod d2_1 t3 t4 d2_2 t5 t6) .
  (* conv_r < refl, prod *) 
  apply coerces_conv_l with (Prod_l A0 B0) ; auto with coc.

  (* conv_r < prod, prod *)
  simpl in H0.
  destruct (inv_eq_prod_l_set t2).
  assert(e0:s0 = x0).
  apply (unique_sort t7 (eq_refl_l t11)).
  assert(e1:s = x0).
  apply (unique_sort t4 (eq_refl_r t11)).
  generalize dependent A ; generalize dependent A'0.
  generalize dependent A' ; generalize dependent A0.
  rewrite e0.
  rewrite <- e1.
  clear e0 e1 x0 s0.
  intros.

  pose (coerces_conv_r t3 t4 t7 d2_1 (tposr_eq_sym t11)).
  
  apply coerces_prod with s ; auto with coc core.

  apply (IH (depth c + depth c1)) with A'0 c c1.
  rewrite H0 ; simpl.
  apply depth_conv_prod.
  auto.
   
  cut(coerce_in_env (A'0 :: e) (A' :: e)) ; intros.
  assert(tposr_wf (A' :: e)).
  apply wf_cons with A' s ; auto with coc.

  destruct (coerce_conv_env c2 H2 H3).
  assert(A' :: e |-- B'0 ~= B0 : s').
  pose (inv_eq_prod_r_set t2).
  apply eq_conv_env with (A0 :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  pose (coerces_conv_r (coerces_sort_l x0) (coerces_sort_r x0) (eq_refl_r H4) x0 H4).
 
  apply (IH (depth c0 + depth d2_2)) with B0 c0 d2_2.
  rewrite H0 ; simpl.
  rewrite e0.
  apply depth_conv_prod2. 
  auto.
  apply coerce_env_hd with s ; auto with coc core.

  (* conv_r  < sum, prod *)
  elim conv_prod_sum with A0 B0 A'0 B'0 ; auto with coc.
  pose (tposr_eq_conv t2) ; auto with coc.

  (* conv_r < sub_l, prod *)
  apply coerces_sub_l ; auto with coc core.
  pose (coerces_conv_r (coerces_sort_l c) t0 t1 c t2).
  apply (IH (depth c0 + depth H1)) with (Prod_l A0 B0) c0 H1 ; auto.
  simpl.
  rewrite H0.
  simpl.
  omega.
  
  (* conv_r < sub_r, prod *)
  elim conv_prod_subset with A0 B0 U' P ; auto with coc.
  pose (tposr_eq_conv t2) ; auto with coc.

  (* conv_r < conv_l, prod *)
  apply coerces_conv_l with B ; auto with coc core.
  
  pose (coerces_conv_r t8 t9 t1 c t2).
  apply (IH (depth c0 + depth H1)) with (Prod_l A0 B0) c0 H1.
  rewrite H0 ; simpl ; auto ; omega.
  auto.

  (* conv_r < conv_r, prod *)
  assert(e |-- B ~= (Prod_l A0 B0) : s0).
  apply tposr_eq_trans with C ; auto with coc.
  pose (coerces_conv_r t7 t8 t1 c H2).

  apply (IH (depth c0 + depth H1)) with (Prod_l A0 B0) c0 H1.
  rewrite H0 ; simpl ; auto.
  auto.
  
  (* conv_r, sum *)
  assert(e |-- Sum_l A' B' -> Sum_l A' B' : s'').
  apply tposr_sum with s s' ; auto with coc.
  destruct c ;
  pose (H1 := coerces_sum d2_1 t3 t4 d2_2 t5 t6 s0 s1) .

  (* conv_r < refl, sum *) 
  apply coerces_conv_l with (Sum_l A0 B0) ; auto with coc.

  (* conv_r < prod, sum *)
  elim conv_prod_sum with A'0 B'0 A0 B0 ; auto with coc.
  pose (tposr_eq_conv t2) ; auto with coc.

  (* conv_r < sum, sum *)
  simpl in H0.
  destruct (inv_eq_sum_l_set t2).
  rewrite <- (unique_sort t4 (eq_refl_r t11)) in t11.
  destruct (inv_eq_sum_r_set t2).
  rewrite <- (unique_sort t10 (eq_refl_l t12)) in t12.
  clear x0 x1.
  assert(s = s2).
  apply (unique_sort (eq_refl_l t11) t7).
  generalize dependent A ; generalize dependent A'0.
  generalize dependent A' ; generalize dependent A0.
  generalize dependent s'0.
  generalize dependent s'.
  rewrite <- H2.
  clear s2 H2 ; intros.
  
  pose (coerces_conv_r t8 t7 t4 c1 t11).

  assert(coerce_in_env (A0 :: e) (A :: e)).
  apply coerce_env_hd with s ; auto with coc.

  assert(coerce_in_env (A'0 :: e) (A :: e)).
  apply coerce_env_hd with s ; auto with coc.

  assert(s' = s'0).
  assert(A'0 :: e |-- B0 -> B0 : s').
  apply typ_conv_env with (A0 ::e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.
  apply coerces_conv_r with A'0 ; auto with coc.
  apply wf_cons with A'0 s ; auto with coc.
  apply (unique_sort H4 (eq_refl_r t12)).
  generalize dependent A ;   generalize dependent A' ;
  generalize dependent A'0 ;   generalize dependent A0 ;
  generalize dependent s. 
  rewrite <- H4.
  clear s'0 H4.
  intros.
  
  apply coerces_sum with s s' ; auto with coc core.

  apply (IH (depth c + depth d2_1)) with A0 c d2_1.
  rewrite H0 ; simpl.
  apply depth_conv_sum.
  auto.

  assert(tposr_wf (A'0 :: e)).
  apply wf_cons with A'0 s ; auto with coc.
  
  assert(coerce_in_env (A0 :: e) (A'0 :: e)).
  apply coerce_env_hd with s ; auto with coc.
  apply coerces_conv_r with A'0 ; auto with coc.

  destruct (coerce_conv_env d2_2 H5 H4).

  pose (coerces_conv_l (eq_refl_l t12) (eq_refl_r t12) (coerces_sort_r x0) t12 x0).

  assert(tposr_wf (A :: e)).
  apply wf_cons with A s ; auto with coc.
  destruct (coerce_conv_env c0 H3 H6).

  apply (IH (depth c2 + depth x1)) with B'0 c2 x1.
  rewrite H0 ; simpl.
  rewrite e1.
  simpl.
  rewrite e0. apply depth_conv_sum2 .
  auto.
  
  (* conv_r  < sub_l, sum *)
  apply coerces_sub_l ; auto with coc core.
  pose (coerces_conv_r (coerces_sort_l c) t0 t1 c t2).
  apply (IH (depth c0 + depth H1)) with (Sum_l A0 B0) c0 H1 ; auto.
  simpl.
  rewrite H0.
  simpl.
  omega.
  
  (* conv_r < sub_r, sum *)
  elim conv_subset_sum with U' P A0 B0 ; auto with coc.
  apply (tposr_eq_conv t2).

  (* conv_r < conv_l, sum *)
  apply coerces_conv_l with B ; auto with coc core.
  
  pose (coerces_conv_r t8 t9 t1 c t2).
  apply (IH (depth c0 + depth H1)) with (Sum_l A0 B0) c0 H1.
  rewrite H0 ; simpl ; auto ; omega.
  auto.

  (* conv_r < conv_r, sum *)
  assert(e |-- B ~= Sum_l A0 B0 : s2).
  apply tposr_eq_trans with C ; auto with coc.
  pose (coerces_conv_r t7 t8 t1 c H2).
  apply (IH (depth c0 + depth H1)) with (Sum_l A0 B0) c0 H1.
  rewrite H0 ; simpl ; auto.
  auto.
  
  (* conv_r, sub_l *)
  pose (coerces_sub_l d2 t3).
  
  generalize H0 ; clear H0.  
  apply (coerces_db_dep (fun e1 T0 C0 s0 => fun d : (e1 |-- T0 >>> C0 : s0) =>
     e1 = e -> T0 = A -> C0 = B -> s0 = set ->     
     x = S (depth d + S (depth d2)) -> e |-- A >>> U' : set))  ; intros ; auto with coc ; try discriminate.

  (* conv_r < refl, sub_l *)
  rewrite <- H0.
  rewrite H1.
  apply (coerces_conv_l t0 t1 (coerces_sort_r d2) t2 c0).

  (* conv_r < prod, sub_l *)
  rewrite <- H3 in t2.
  elim conv_prod_subset with A' B' U P ; auto.
  apply (tposr_eq_conv t2).

  (* conv_r < sum, sub_l *)
  rewrite <- H3 in t2.
  elim conv_subset_sum with U P A' B' ; auto with coc.
  pose (tposr_eq_conv t2) ; auto with coc.

  (* conv_r < sub_l, sub_l *)
  clear H.
  generalize dependent e.
  generalize dependent e0.
  rewrite H2.
  rewrite <- H1.
  intros.
  
  generalize dependent U0.
  rewrite H0.
  intros.
  apply coerces_sub_l ; auto.
  
  pose (coerces_conv_l t0 t1 (coerces_sort_r c0) t2 c0).
  apply (IH (depth c1 + depth c2)) with B c1 c2 ; auto.
  rewrite H4 ; simpl.
  omega.
  
  (* conv_r < sub_r, sub_l *)
  clear H.
  generalize dependent e.
  generalize dependent e0.
  rewrite <- H2.
  rewrite <- H1.
  intros.
  generalize dependent U0.
  generalize dependent U'0.
  rewrite H0.
  intros.
  pose (inv_eq_subset_l_set t2).

  pose (coerces_conv_r (coerces_sort_l c1) (coerces_sort_r c1) (eq_refl_r t5) c1 t5). 
  apply (IH (depth c2 + depth d2)) with U c2 d2 ; auto.
  rewrite H4 ; simpl.
  omega.
  
  (* conv_r < conv_l, sub_l *)
  clear H.
  generalize dependent s.
  rewrite H0.
  rewrite <- H1.
  intros.
  apply coerces_conv_l with B0 ; auto with coc.
  rewrite <- H3 ; auto.
  rewrite <- H3 ; auto.
  apply (coerces_sort_r d2).
  rewrite H3 in t7.
  assumption.
  generalize dependent e.
  rewrite H2.
  rewrite H3.
  intros.
  pose (coerces_conv_r t5 t6 t1 c1 t2).
  apply (IH (depth c2 + depth c0)) with (Subset_l U P) c2 c0 ; auto.
  rewrite H4 ; simpl.
  omega.
  
  (* conv_r < conv_l, sub_l *)
  clear H.
  generalize dependent e0.
  rewrite H1.
  rewrite H3.
  intros.
  
  assert(e |-- B0 ~= (Subset_l U P) : set).
  apply tposr_eq_trans with C ; auto.
  rewrite <- H0 ; assumption.
  rewrite H2 ; auto with coc.
  
  generalize dependent A.
  generalize dependent B0.
  generalize dependent t6.
  rewrite H0.
  intros.
  pose (coerces_conv_r t4 t5 t1 c1 H).
  apply (IH (depth c2 + depth c0)) with (Subset_l U P) c2 c0 ; auto.
  rewrite H4 ; simpl.
  omega.

  (* conv_r, sub_r *)
  apply coerces_sub_r ; auto with coc.
  pose (coerces_conv_r t t0 t1 c t2).
  apply (IH (depth c0 + depth d2)) with U c0 d2.
  rewrite H0 ; simpl ; try omega ; auto.
  auto.

  (* conv_r, conv_l *)
  assert (e |-- B ~= B0 : s).
  apply tposr_eq_trans with A0 ; auto with coc.
  pose (coerces_conv_r t t0 t4 c H).
  apply (IH (depth c0 + depth d2)) with B0 c0 d2.
  rewrite H0 ; simpl ; try omega ; auto.
  auto.

  (* conv_r, conv_r *)
  apply coerces_conv_r with B0 ; auto with coc.
  pose (coerces_conv_r t t0 t1 c t2).
  apply (IH (depth c0 + depth d2)) with A0 c0 d2.
  rewrite H0 ; simpl ; try omega ; auto.
  auto.
Qed.

Theorem coerce_trans_db_set : forall e A B C s, e |-- A >>> B : s -> e |-- B >>> C : s ->
  e |-- A >>> C : s.
Proof.
  intros.
  set (x := depth H).
  set (y := depth H0).
  set (sum := x + y).
  apply (@coerce_trans_aux sum e A B s H C H0).
  unfold sum, x, y.
  reflexivity.
Qed.

Require Import Lambda.TPOSR.TypesDepth.

Theorem coerces_db_depth : forall e T U s n1, Depth.coerces_db e T U s n1 -> 
  exists d : (Narrowing.coerces_db e T U s), depth d = n1.
Proof.
  intros.
  induction H.
  
  exists (Narrowing.coerces_refl H).
  simpl ; auto.

  destruct IHcoerces_db1.
  destruct IHcoerces_db2.
  exists (Narrowing.coerces_prod x H0 H1 x0 H3 H4).
  simpl ; auto.

  destruct IHcoerces_db1.
  destruct IHcoerces_db2.
  exists (Narrowing.coerces_sum x H0 H1 x0 H3 H4 H5 H6).
  simpl ; auto.

  destruct IHcoerces_db.
  exists (Narrowing.coerces_sub_l x H0).
  simpl ; auto.

  destruct IHcoerces_db.
  exists (Narrowing.coerces_sub_r x H0).
  simpl ; auto.

  destruct IHcoerces_db.
  exists (Narrowing.coerces_conv_l H H0 H1 H2 x).
  simpl ; auto.

  destruct IHcoerces_db.
  exists (Narrowing.coerces_conv_r H H0 H1 x H3).
  simpl ; auto.
Qed.

Theorem depth_coerces_db : forall e T U s, Narrowing.coerces_db e T U s -> exists n, 
 Depth.coerces_db e T U s n.
Proof.
  induction 1 ; intros ; auto with coc core.
  exists 0 ; auto with coc.

  destruct IHcoerces_db1.
  destruct IHcoerces_db2.
  exists (S (max x x0)) ; simpl ; auto with coc.
  apply Depth.coerces_prod with s ; auto.

  destruct IHcoerces_db1.
  destruct IHcoerces_db2.
  exists (S (max x x0)) ; simpl ; auto with coc.
  apply Depth.coerces_sum with s s' ; auto.

  destruct IHcoerces_db.
  exists (S x) ; simpl ; auto with coc.

  destruct IHcoerces_db.
  exists (S x) ; simpl ; auto with coc.

  destruct IHcoerces_db.
  exists (S x) ; simpl ; auto with coc.
  apply coerces_conv_l with B ; auto with coc.

  destruct IHcoerces_db.
  exists (S x) ; simpl ; auto with coc.
  apply coerces_conv_r with B ; auto with coc.
Qed.

Theorem coerce_trans_d : forall e A B C s n1 n2, e |-- A >>> B : s [n1] -> e |-- B >>> C : s [n2]->
  exists m, e |-- A >>> C : s [m].
Proof.
  intros.
  destruct (coerces_db_depth H).
  destruct (coerces_db_depth H0).
  pose (coerce_trans_db_set x x0).
  exact (depth_coerces_db c).
Qed.

Theorem coerce_trans : forall e A B C s, e |-- A >> B : s -> e |-- B >> C : s -> e |-- A >> C : s.
Proof.
  intros.
  destruct (coerce_coerces_db H).
  destruct (coerce_coerces_db H0).
  destruct (coerce_trans_d H1 H2).
  exact (coerces_db_coerce H3).
Qed.


