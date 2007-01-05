Require Import Lambda.Utils.
Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.Russell.Types.
Require Import Lambda.Russell.Thinning.
Require Import Lambda.Russell.Substitution.
Require Import Lambda.Russell.Generation.
Require Import Lambda.Russell.UnicityOfSorting.
Require Import Lambda.Russell.Narrowing.
Require Import Lambda.Russell.Injectivity.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

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

Lemma coerces_sort_l : forall e T U s, e |-- T >>> U : s -> e |-- T : Srt s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc core.
  apply type_prod with s ; auto with coc.
  apply type_sum with s s' ; auto with coc.
  apply type_subset ; auto with coc.
Qed.

Lemma coerces_sort_r : forall e T U s, e |-- T >>> U : s -> e |-- U : Srt s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc core.
  apply type_prod with s ; auto with coc.
  apply type_sum with s s' ; auto with coc.
  apply type_subset ; auto with coc.
Qed.

Theorem coerce_trans_aux : forall n : nat,
(forall e A B s, forall d1 : e |-- A >>> B : s, 
forall C, forall d2 : e |-- B >>> C : s,
  n = (depth d1) + (depth d2) ->
  e |-- A >>> C : s).
Proof.
  intros n.
  pattern n.
  apply (wf_lt_induction_type).

  intros x IH.
  simple induction d1 ;  auto with coc.

 clear e A B s d1; intros ; clear H H0.
 generalize H1 ; clear H1.
   apply (coerces_db_dep (fun e1 T0 C0 s0 => fun d : (e1 |-- T0 >>> C0 : s0) =>
     e1 = e -> T0 = Prod A' B' -> C0 = C -> s0 = s' ->     
     (x = depth (coerces_prod c t t0 c0 t1 t2) + depth d) ->
     e |-- Prod A B >>> C0 : s')) ; intros ; auto with coc ; try discriminate.

  (* prod, refl *)
  rewrite H0 ;
  apply coerces_prod with s ; auto with coc.
  
  (* prod, prod *)
  clear H ; clear H0.
  simpl in H5.
  inversion H2.
  generalize dependent c1.
  generalize dependent t3 ; generalize dependent t4.
  generalize dependent c2 ; generalize dependent t5 ; generalize dependent t6.
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

  assert(e |-- A'0 >>> A : s).
  apply (IH (depth c1 + depth c)) with A' c1 c ; auto.
  rewrite H5.
  simpl.
  apply depth_prod_prod_l.

  cut(coerce_in_env (A' :: e) (A'0 :: e)) ; intros.
  assert(wf (A'0 :: e)).
  apply wf_var with s0 ; auto with coc.
  rewrite <- e1  ; auto.
  destruct (coerce_conv_env c0 H1 H7).
  
  apply coerces_prod with s ; auto with coc.
  
  apply (IH (depth x0 + depth c2)) with B' x0 c2 ; auto.
  rewrite e2.
  rewrite H5.
  simpl.
  apply depth_prod_prod_r.
  apply coerce_env_hd with s ; auto with coc.

  (* prod, subset *)
  clear H.
  simpl in H4.
  rewrite <- H3.
  apply coerces_sub_r.
  generalize dependent c1.
  rewrite H1 ; rewrite H0.
  intros.
  generalize dependent e.
  rewrite <- H3.
  intros.
  pose (coerces_prod c t t0 c0 t1 t2).
  set (dc2 := depth c2).
  apply (IH (depth c2 + depth c1)) with (Prod A' B') c2 c1 ; auto.
  rewrite H4.
  simpl.
  omega.
  
  rewrite <- H0 ; auto.

  (* prod, conv_l *)
  clear H.
  simpl in H4.
  generalize dependent c1 ; generalize dependent c2.
  generalize dependent t3 ; generalize dependent t4 ; generalize dependent t5.
  rewrite H0.
  rewrite H1.
  rewrite H2.
  rewrite H3.
  clear H0 H1 H2 H3.
  intros.
  clear d2.

  assert(e |-- Prod A B : Srt s').
  apply type_prod with s ; auto with coc.
  assert(e |-- Prod A B >>> Prod A' B' : s').
  apply coerces_prod with s ; auto with coc.

  destruct c2.

  (* prod, conv_l < refl *) 
  apply coerces_conv_r with (Prod A' B') ; auto with coc.

  (* prod, conv_l < prod *)
  simpl in H4.
  pose (H1 := t).
  pose (H2:=inv_conv_prod_sort_l_set t3 t4 c1 t).
  intuition.
  assert (e1:=unique_sort t7 H2).
  rewrite <- e1 in H1.
  assert (e2:=unique_sort H1 t).
  generalize dependent A'0.
  rewrite e2.
  intros.

  assert(e |-- A'0 >>> A : s).
  pose (inv_conv_prod_l _ _ _ _ c1).
  pose(coerces_conv_l).
  rewrite e2 in t7.
  set (d := coerces_conv_l t7 t t0 (sym_conv _ _ c2) c).
  apply (IH (depth c2_1 + depth d)) with A1 c2_1 d ; auto with coc.
  simpl.
  rewrite H4 ; simpl.
  apply depth_prod_conv_prod.
  
  apply coerces_prod with s ; auto with coc core.

  cut(coerce_in_env (A' :: e) (A'0 :: e)) ; intros.
  assert(wf (A'0 :: e)).
  apply wf_var with s ; auto with coc.

  cut(A'0 :: e |-- B' : Srt s') ; intros.
  cut(A'0 :: e |-- B0 : Srt s') ; intros.
  pose (inv_conv_prod_r _ _ _ _ c1).
  set (d := coerces_conv_l H7 H8 t9 c2 c2_2).
  destruct (coerce_conv_env c0 H5 H6).
  apply (IH (depth c0 + depth d)) with B' x0 d ; auto with coc.
  simpl.
  rewrite H4.
  apply depth_prod_conv_prod2.

  apply (coerces_sort_l c2_2).
  apply (typ_conv_env t2 H5 H6).

  apply coerce_env_hd with s ; auto with coc core.
  apply coerces_conv_r with A1 ; auto with coc core.
  rewrite e2 in t7.
  apply (sym_conv _ _ (inv_conv_prod_l _ _ _ _ c1)).

  (* prod, conv_l < sum *)
  elim conv_prod_sum with A' B' A1 B0 ; auto with coc.

  (* prod, conv_l < sub_l *)
  elim conv_prod_subset with A' B' U P ; auto with coc.
  
  (* prod, conv_l < sub_r *)
  apply coerces_sub_r ; auto with coc core.
  pose (coerces_conv_l t3 t4 (coerces_sort_r c2) c1 c2).
  pose (coerces_prod c t t0 c0 t1 t2).
  apply (IH (depth c4 + depth c3)) with (Prod A' B') c4 c3 ; auto.
  simpl.
  rewrite H4.
  simpl.
  omega.

  (* prod, conv_l < conv_l *)
  assert(conv (Prod A' B') B0).
  apply trans_conv_conv with A1 ; auto with coc.
  pose (coerces_conv_l t3 t7 t8 H1 c3).
  pose (coerces_prod c t t0 c0 t1 t2).
  apply (IH (depth c5 + depth c4)) with (Prod A' B') c5 c4.
  rewrite H4 ; simpl ; auto ; omega.
  auto.

  (* prod, conv_l < conv_r *)
  apply coerces_conv_r with B0 ; auto with coc.

  pose (coerces_prod c t t0 c0 t1 t2).
  pose (coerces_conv_l t3 t6 t7 c1 c2).
  apply (IH (depth c4 + depth c5)) with (Prod A' B') c4 c5.
  rewrite H4 ; simpl ; auto.
  omega.
  auto.

   (* prod, conv_r *)
   clear H.
  simpl in H4.
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
   apply type_prod with s ; auto with coc.

   pose (coerces_prod c t t0 c0 t1 t2).
   apply (IH (depth c3 + depth c1)) with (Prod A' B') c3 c1.
   rewrite H4.
   simpl.
   omega.
   auto.

 clear e A B s d1; intros; clear H H0.
 generalize H1 ; clear H1.
 rename s0 into sum_sort0.
 rename s1 into sum_sort1.
   apply (coerces_db_dep (fun e1 T0 C0 s0 => fun d : (e1 |-- T0 >>> C0 : s0) =>
     e1 = e -> T0 = Sum A' B' -> C0 = C -> s0 = s'' ->     
     (x = depth (coerces_sum c t t0 c0 t1 t2 sum_sort0 sum_sort1) + depth d) ->
     e |-- Sum A B >>> C0 : s'')) ; intros ; auto with coc ; try discriminate.

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
  assert(wf (A :: e)).
  apply wf_var with s ; auto with coc.
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
  pose (generation_subset t4).
  inversion e1.
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
  apply (IH (depth c2 + depth c1)) with (Sum A' B') c2 c1 ; auto.
  rewrite H4.
  simpl.
  omega.
  
  rewrite <- H0 ; auto.

  (* sum, conv_l *)
  clear H.
  simpl in H4.
  generalize dependent c1 ; generalize dependent c2.
  generalize dependent t3 ; generalize dependent t4 ; generalize dependent t5.
  rewrite H0.
  rewrite H1.
  rewrite H2.
  rewrite H3.
  clear H0 H1 H2 H3.
  intros.
  clear d2.

  assert(e |-- Sum A B : Srt s'').
  apply type_sum with s s' ; auto with coc.
  assert(e |-- Sum A' B' : Srt s'').
  apply type_sum with s s' ; auto with coc.
  assert(e |-- Sum A B >>> Sum A' B' : s'').
  apply coerces_sum with s s' ; auto with coc.
  
  destruct c2.

  (* sum, conv_l < refl *) 
  apply coerces_conv_r with (Sum A' B') ; auto with coc.

  (* sum, conv_l < prod *)
  elim conv_prod_sum with A1 B0 A' B'; auto with coc.

  (* sum, conv_l < sum *)
  simpl in H4.
  pose (H3:=inv_conv_sum_sort_l_set t3 t4 c1 t).
  pose (unique_sort t7 H3).
  generalize dependent A'0.
  rewrite e1.
  intros.
  
  assert(e |-- A >>> A'0 : s).
  pose (inv_conv_sum_l _ _ _ _ c1).
  set (d := coerces_conv_l t H3 t6 c2 c2_1).
  apply (IH (depth c + depth d)) with A' c d ; auto with coc.
  simpl.
  rewrite H4 ; simpl.
  apply depth_sum_conv_sum2.

  pose (H6:=inv_conv_sum_sort_r_set t3 t4 c1 t2).
  assert(A' :: e |-- B0 : Srt s'0).
  apply typ_conv_env with (A1 :: e) ; auto with coc.
  pose (inv_conv_sum_sort_l_set t3 t4 c1 t).
  apply coerce_env_hd with s ; intuition ; auto with coc.
  apply coerces_conv_l with A1 ; auto with coc.
  exact (inv_conv_sum_l _ _ _ _ c1).
  apply wf_var with s ; auto with coc.

  apply coerces_sum with s s' ; auto with coc core.

  assert (Heq:=unique_sort H6 H5).

  cut(coerce_in_env (A1 :: e) (A :: e)) ; intros.
  assert(wf (A :: e)).
  apply wf_var with s ; auto with coc.

  generalize dependent B'.
  generalize dependent B'0.
  generalize dependent B0.
  rewrite <- Heq.
  intros.

  cut(A :: e |-- B' : Srt s') ; intros.
  cut(A :: e |-- B0 : Srt s') ; intros.
  cut(A :: e |-- B'0 : Srt s') ; intros.
  pose (inv_conv_sum_r _ _ _ _ c1).
  
  destruct (coerce_conv_env c2_2 H7 H8).
  set (d := coerces_conv_l H9 H10 H11 c2 x0).
  apply (IH (depth c0 + depth d)) with B' c0 d ; auto with coc.
  simpl.
  rewrite H4.
  rewrite e2.
  apply depth_prod_conv_prod2.

  apply typ_conv_env with (A'0 :: e) ; auto with coc.
  apply coerce_env_hd with s ; auto with coc.

  apply typ_conv_env with (A1 :: e) ; auto with coc.
  apply (coerces_sort_r c0).

  apply coerce_env_hd with s ; auto with coc.
  apply coerces_conv_r with A' ; auto with coc core.
  apply (inv_conv_sum_l _ _ _ _ c1).
  rewrite <- (unique_sort H5 H6).
  assumption.

  (* sum, conv_l < sub_l *)
  elim conv_subset_sum with U P  A' B' ; auto with coc.
 
  (* sum, conv_l < sub_r *)
  apply coerces_sub_r ; auto with coc core.
  pose (coerces_conv_l t3 t4 (coerces_sort_r c2) c1 c2).
  pose (coerces_sum c t t0 c0 t1 t2 sum_sort0 sum_sort1).
  apply (IH (depth c4 + depth c3)) with (Sum A' B') c4 c3 ; auto.
  simpl.
  rewrite H4.
  simpl.
  omega.

  (* sum, conv_l < conv_l *)
  assert(conv (Sum A' B') B0).
  apply trans_conv_conv with A1 ; auto with coc.
  pose (coerces_conv_l t3 t7 t8 H2 c3).
  pose (coerces_sum c t t0 c0 t1 t2 sum_sort0 sum_sort1).
  apply (IH (depth c5 + depth c4)) with (Sum A' B') c5 c4.
  rewrite H4 ; simpl ; auto ; omega.
  auto.

  (* sum, conv_l < conv_r *)
  apply coerces_conv_r with B0 ; auto with coc.

  pose (coerces_sum c t t0 c0 t1 t2 (sum_sort0) sum_sort1).
  pose (coerces_conv_l t3 t6 t7 c1 c2).
  apply (IH (depth c4 + depth c5)) with (Sum A' B') c4 c5.
  rewrite H4 ; simpl ; auto.
  omega.
  auto.

   (* sum, conv_r *)
   clear H.
  simpl in H4.
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
   apply type_sum with s s' ; auto with coc.

   pose (coerces_sum c t t0 c0 t1 t2 sum_sort0 sum_sort1).
   apply (IH (depth c3 + depth c1)) with (Sum A' B') c3 c1.
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
     e1 = e -> T0 = Subset U' P -> C0 = C -> s0 = set ->     
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
  apply (IH (depth c1 + depth c0)) with (Subset U' P) c1 c0.
  rewrite H5 ; simpl ; auto.
  omega.
  auto.

  (* sub_r, conv_l *)
  clear H0.
  simpl in H5.
  generalize dependent s.
  rewrite H1.
  rewrite H2 in c0.
  rewrite H2.
  rewrite H3.
  intros.
  pose (HUset := coerces_sort_l c).
  pose (HU'set := coerces_sort_r c).

  clear d2.
  destruct c1.
  
  (* sub_r, conv_l < refl *)
 apply coerces_conv_r with (Subset U' P)  ; auto with coc.
  rewrite <- H4 ; auto.
  rewrite <- H4 ; auto.

  (* sub_r, conv_l < prod *)
  elim conv_prod_subset with A0 B U' P ; auto with coc.

  (* sub_r, conv_l < sum *)
  elim conv_subset_sum with U' P A0 B ; auto with coc.

  (* sub_r, conv_l < sub_l *)
  pose (inv_conv_subset_l _ _ _ _ c0).
  
  pose (coerces_conv_r (coerces_sort_l c) (coerces_sort_r c) (coerces_sort_l c1) c c2).
  apply (IH (depth c1 + depth c3)) with U0 c3 c1.
  rewrite H5 ; simpl.
  omega.
  auto with arith.

  (* sub_r, conv_l < sub_r *)
  apply coerces_sub_r ; auto.
  pose (coerces_conv_l t0 t1 (coerces_sort_r c1) c0 c1).
  pose (coerces_sub_r c t).
  apply (IH (depth c3 + depth c2)) with (Subset U' P) c3 c2 ; auto.
  rewrite H5 ; simpl.
  omega.
  auto with arith.
  
  (* sub_r, conv_l < conv_l *)
  assert (conv (Subset U' P) B).
  apply trans_conv_conv with A0 ; auto.
  pose (coerces_sub_r c t).
  pose (coerces_conv_l t0 t4 t5 H0 c2).
  generalize dependent e.
  rewrite H4.
  intros.
  apply (IH (depth c3 + depth c4)) with (Subset U' P) c3 c4 ; auto.
  rewrite H5 ; simpl.
  omega.

  (* sub_r, conv_l < conv_r *)
  generalize dependent e.
  rewrite H4.
  intros.
  apply coerces_conv_r with B ; auto with coc.
  pose (coerces_sub_r c t).
  pose (coerces_conv_l t0 t3 t4 c0 c1).
  apply (IH (depth c3 + depth c4)) with (Subset U' P) c3 c4 ; auto.
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
  apply (IH (depth c2 + depth c0)) with (Subset U' P) c2 c0 ; auto.
  rewrite H5 ; simpl.
  omega.

  (* conv_l *)
  intros.
  apply coerces_conv_l with B0 ; auto with coc.
  apply (coerces_sort_r d2).
  apply (IH (depth c0 + depth d2)) with C c0 d2.
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
  assert(e |-- Prod A' B' : Srt s').
  apply type_prod with s ; auto with coc.
  destruct c ;
  pose (H1 := coerces_prod d2_1 t2 t3 d2_2 t4 t5) .
  (* conv_r < refl, prod *) 
  apply coerces_conv_l with (Prod A0 B0) ; auto with coc.

  (* conv_r < prod, prod *)
  simpl in H0.
  assert (H3:=inv_conv_prod_sort_l_set t0 t1 c0 t6).
  assert (H2:=t6).
  pose (unique_sort t6 H2).
  pose (unique_sort t3 H3).
  generalize dependent A ; generalize dependent A'0.
  rewrite <- e1.
  intros.
  generalize dependent A' ; generalize dependent A0.
  generalize dependent c1 ; generalize dependent t7.
  intros.
  clear e0 ; clear e1.

  pose (inv_conv_prod_l _ _ _ _ c0).
  pose (coerces_conv_r t2 t3 H2 d2_1 (sym_conv _ _ c)).
  
  apply coerces_prod with s ; auto with coc core.

  apply (IH (depth c3 + depth c1)) with A'0 c3 c1.
  rewrite H0 ; simpl.
  apply depth_conv_prod.
   auto.
   
  cut(coerce_in_env (A'0 :: e) (A' :: e)) ; intros.
  assert(wf (A' :: e)).
  apply wf_var with s ; auto with coc.

  destruct (coerce_conv_env c2 H4 H5).

  pose (inv_conv_prod_r _ _ _ _ c0).
  pose (coerces_conv_r (coerces_sort_l x0) (coerces_sort_r x0) (coerces_sort_l d2_2) x0 c4).
  
  apply (IH (depth c5 + depth d2_2)) with B0 c5 d2_2.
  rewrite H0 ; simpl.
  rewrite e0.
  apply depth_conv_prod2. 
  auto.
  apply coerce_env_hd with s ; auto with coc core.

  (* conv_r  < sum, prod *)
  elim conv_prod_sum with A0 B0 A'0 B'0 ; auto with coc.

  (* conv_r < sub_l, prod *)
  apply coerces_sub_l ; auto with coc core.
  pose (coerces_conv_r (coerces_sort_l c) t0 t1 c c0).
  apply (IH (depth c1 + depth H1)) with (Prod A0 B0) c1 H1 ; auto.
  simpl.
  rewrite H0.
  simpl.
  omega.
  
  (* conv_r < sub_r, prod *)
  elim conv_prod_subset with A0 B0 U' P ; auto with coc.

  (* conv_r < conv_l, prod *)
  apply coerces_conv_l with B ; auto with coc core.
  
  pose (coerces_conv_r t7 t8 t1 c1 c0).
  apply (IH (depth c2 + depth H1)) with (Prod A0 B0) c2 H1.
  rewrite H0 ; simpl ; auto ; omega.
  auto.

  (* conv_r < conv_r, prod *)
  assert(conv B (Prod A0 B0)).
  apply trans_conv_conv with C ; auto with coc.
  pose (coerces_conv_r t6 t7 t1 c H2).

  apply (IH (depth c2 + depth H1)) with (Prod A0 B0) c2 H1.
  rewrite H0 ; simpl ; auto.
  auto.
  
  (* conv_r, sum *)
  assert(e |-- Sum A' B' : Srt s'').
  apply type_sum with s s' ; auto with coc.
  destruct c ;
  pose (H1 := coerces_sum d2_1 t2 t3 d2_2 t4 t5 s0 s1) .

  (* conv_r < refl, sum *) 
  apply coerces_conv_l with (Sum A0 B0) ; auto with coc.

  (* conv_r < prod, sum *)
  elim conv_prod_sum with A'0 B'0 A0 B0 ; auto with coc.

  (* conv_r < sum, sum *)
  simpl in H0.
  assert (H3:=inv_conv_sum_sort_l_set t0 t1 c0 t6).
  assert (H2:=t6).
  intuition.
  pose (unique_sort t6 H2).
  pose (unique_sort t3 H3).
  generalize dependent A ; generalize dependent A'0.
  rewrite <- e1.
  intros.
  generalize dependent A' ; generalize dependent A0.
  generalize dependent c1 ; generalize dependent t7.
  intros.
  clear e0 ; clear e1.
  assert(s' = s'0).
  inversion s0 ; inversion s3 ; intuition ; try discriminate.
  rewrite H5 ; rewrite H7 ; auto.
  rewrite H10 in H9 ; discriminate.
  rewrite H10 in H9 ; discriminate.
  rewrite H5 ; rewrite H7 ; auto.

  pose (inv_conv_sum_l _ _ _ _ c0).
  pose (coerces_conv_r t7 H2 t3 c1 c).
  
  apply coerces_sum with s s' ; auto with coc core.

  apply (IH (depth c3 + depth d2_1)) with A0 c3 d2_1.
  rewrite H0 ; simpl.
  apply depth_conv_sum.
  auto.

  cut(coerce_in_env (A0 :: e) (A :: e)) ; intros.
  assert(wf (A :: e)).
  apply wf_var with s ; auto with coc.

  pose (inv_conv_sum_r _ _ _ _ c0).
  destruct (coerce_conv_env d2_2 H5 H6).
  generalize dependent e.
  rewrite <- H4.
  intros.
  pose (coerces_conv_l (coerces_sort_r c2) (coerces_sort_l x0) (coerces_sort_r x0) c4 x0).
  
  apply (IH (depth c2 + depth c5)) with B'0 c2 c5.
  rewrite H0 ; simpl.
  rewrite e0. apply depth_conv_sum2 .
  auto.
  apply coerce_env_hd with s ; auto with coc core.
  rewrite H4.
  assumption.

  (* conv_r  < sub_l, sum *)
  apply coerces_sub_l ; auto with coc core.
  pose (coerces_conv_r (coerces_sort_l c) t0 t1 c c0).
  apply (IH (depth c1 + depth H1)) with (Sum A0 B0) c1 H1 ; auto.
  simpl.
  rewrite H0.
  simpl.
  omega.
  
  (* conv_r < sub_r, sum *)
  elim conv_subset_sum with U' P A0 B0 ; auto with coc.

  (* conv_r < conv_l, sum *)
  apply coerces_conv_l with B ; auto with coc core.
  
  pose (coerces_conv_r t7 t8 t1 c1 c0).
  apply (IH (depth c2 + depth H1)) with (Sum A0 B0) c2 H1.
  rewrite H0 ; simpl ; auto ; omega.
  auto.

  (* conv_r < conv_r, sum *)
  assert(conv B (Sum A0 B0)).
  apply trans_conv_conv with C ; auto with coc.
  pose (coerces_conv_r t6 t7 t1 c H2).
  apply (IH (depth c2 + depth H1)) with (Sum A0 B0) c2 H1.
  rewrite H0 ; simpl ; auto.
  auto.
  
  (* conv_r, sub_l *)
  pose (coerces_sub_l d2 t2).
  
  generalize H0 ; clear H0.  
  apply (coerces_db_dep (fun e1 T0 C0 s0 => fun d : (e1 |-- T0 >>> C0 : s0) =>
     e1 = e -> T0 = A -> C0 = B -> s0 = set ->     
     x = S (depth d + S (depth d2)) -> e |-- A >>> U' : set))  ; intros ; auto with coc ; try discriminate.

  (* conv_r < refl, sub_l *)
  rewrite <- H0.
  rewrite H1.
  apply (coerces_conv_l t0 t1 (coerces_sort_r d2) c0 c1).

  (* conv_r < prod, sub_l *)
  rewrite <- H3 in c0.
  elim conv_prod_subset with A' B' U P ; auto.

  (* conv_r < sum, sub_l *)
  rewrite <- H3 in c0.
  elim conv_subset_sum with U P A' B' ; auto with coc.

  (* conv_r < sub_l, sub_l *)
  clear H.
  generalize dependent e.
  generalize dependent e0.
  generalize dependent c0.
  rewrite H2.
  rewrite <- H1.
  intros.
  
  generalize dependent U0.
  rewrite H0.
  intros.
  apply coerces_sub_l ; auto.
  
  pose (coerces_conv_l t0 t1 (coerces_sort_r c1) c0 c1).
  apply (IH (depth c2 + depth c3)) with B c2 c3 ; auto.
  rewrite H4 ; simpl.
  omega.
  
  (* conv_r < sub_r, sub_l *)
  clear H.
  generalize dependent e.
  generalize dependent e0.
  generalize dependent c0.
  rewrite <- H2.
  rewrite <- H1.
  intros.
  generalize dependent U0.
  generalize dependent U'0.
  rewrite H0.
  intros.
  pose (inv_conv_subset_l _ _ _ _ c0).
  pose (coerces_conv_r t (coerces_sort_r c2) (coerces_sort_l d2) c2 c3). 
  apply (IH (depth c4 + depth d2)) with U c4 d2 ; auto.
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
  generalize dependent e.
  rewrite H2.
  rewrite H3.
  intros.
  pose (coerces_conv_r t4 t5 t1 c3 c0).
  apply (IH (depth c4 + depth c1)) with (Subset U P) c4 c1 ; auto.
  rewrite H4 ; simpl.
  omega.
  
  (* conv_r < conv_l, sub_l *)
  clear H.
  generalize dependent e0.
  rewrite H1.
  rewrite H3.
  intros.
  
  assert(conv B0 (Subset U P)).
  apply trans_conv_conv with C ; auto.
  rewrite H2 ; assumption.
  
  generalize dependent A.
  generalize dependent B0.
  generalize dependent t5.
  rewrite H0.
  intros.
  pose (coerces_conv_r t3 t4 t1 c2 H).
  apply (IH (depth c4 + depth c1)) with (Subset U P) c4 c1 ; auto.
  rewrite H4 ; simpl.
  omega.

  (* conv_r, sub_r *)
  apply coerces_sub_r ; auto with coc.
  pose (coerces_conv_r t t0 t1 c c0).
  apply (IH (depth c1 + depth d2)) with U c1 d2.
  rewrite H0 ; simpl ; try omega ; auto.
  auto.

  (* conv_r, conv_l *)
  assert (conv B B0).
  apply trans_conv_conv with A0 ; auto with coc.
  pose (coerces_conv_r t t0 t3 c H).
  apply (IH (depth c2 + depth d2)) with B0 c2 d2.
  rewrite H0 ; simpl ; try omega ; auto.
  auto.

   (* conv_r, conv_r *)
   apply coerces_conv_r with B0 ; auto with coc.
   pose (coerces_conv_r t t0 t1 c c0).
  apply (IH (depth c2 + depth d2)) with A0 c2 d2.
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

Require Import Lambda.Russell.Depth.

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


