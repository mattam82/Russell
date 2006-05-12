Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.
Require Import CCPD.Thinning.
Require Import CCPD.Substitution.
Require Import CCPD.Generation.
Require Import CCPD.UnicityOfSorting.
Require Import CCPD.Narrowing.

Set Implicit Arguments.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Lemma inv_conv_prod_sort_l : forall e U V U' V' s, e |- Prod U V : Srt s -> e |- Prod U' V' : Srt s ->
  conv (Prod U V) (Prod U' V') -> { s1 : sort | e |- U : Srt s1 /\ e |- U' : Srt s1 }. 
Admitted.

Lemma inv_conv_prod_sort_r : forall e U V U' V' s, e |- Prod U V : Srt s -> e |- Prod U' V' : Srt s ->
  conv (Prod U V) (Prod U' V') -> { s2 : sort | U' :: e |- V : Srt s2 /\ U' :: e |- V : Srt s2 }. 
Admitted.

Lemma inv_conv_sum_sort_l : forall e U V U' V' s, e |- Sum U V : Srt s -> e |- Sum U' V' : Srt s ->
  conv (Sum U V) (Sum U' V') -> { s1 : sort | e |- U : Srt s1 /\ e |- U' : Srt s1 }. 
Admitted.

Lemma inv_conv_sum_sort_r : forall e U V U' V' s, e |- Sum U V : Srt s -> e |- Sum U' V' : Srt s ->
  conv (Sum U V) (Sum U' V') -> { s2 : sort | U' :: e |- V : Srt s2 /\ U' :: e |- V : Srt s2 }. 
Admitted.


Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Arith.Wf_nat.
(*
Definition lex_nat := lexprod nat (fun _ => nat) lt (fun _ => lt).

Lemma wf_lex : well_founded lex_nat.
Proof.
  unfold lex_nat.
  apply wf_lexprod ; auto with coc.
  apply lt_wf.
  intros ; apply lt_wf.
Qed.

Check existS.
Check nat.

Definition build_pair (x y : nat) := existS (fun _ => nat) x y.

Check (well_founded_induction).
Check build_pair.
Definition pair_t := sigS (fun _ : nat => nat).



Lemma wf_lex_induction_type : forall (P : pair_t -> Type),
  (forall x : pair_t, (forall y : pair_t, lex_nat y x -> P y) -> P x) ->
       forall a : pair_t, P a.
Proof.
apply (well_founded_induction_type).
apply wf_lex.
Qed.
*)

Lemma wf_lt_induction_type : forall (P : nat -> Type),
  (forall x : nat, (forall y : nat, y < x -> P y) -> P x) ->
       forall a : nat, P a.
Proof.
apply (well_founded_induction_type).
apply lt_wf.
Qed.

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

Lemma coerces_sort_l : forall e T U s, e |- T >>> U : s -> e |- T : Srt s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc core.
  apply type_prod with s ; auto with coc.
  apply type_sum with s ; auto with coc.
  apply type_subset ; auto with coc.
Qed.

Lemma coerces_sort_r : forall e T U s, e |- T >>> U : s -> e |- U : Srt s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc core.
  apply type_prod with s ; auto with coc.
  apply type_sum with s ; auto with coc.
  apply type_subset ; auto with coc.
Qed.

Lemma coerces_sym : forall e T U s, forall d1 : e |- T >>> U : s,
  { d2 : e |- U >>> T : s | depth d2 = depth d1 }.
Proof.
  induction d1 ;  simpl ; intros ; auto with coc.

  exists (coerces_refl t) ; simpl ; auto.

  destruct IHd1_1.
  destruct IHd1_2.
(*  exists (coerces_prod x t0 t x0 t1 t2).*)
Admitted.




Theorem coerce_trans : forall n : nat,
(forall e A B s, forall d1 : e |- A >>> B : s, 
forall C, forall d2 : e |- B >>> C : s,
  n = (depth d1) + (depth d2) ->
  e |- A >>> C : s).
Proof.
  intros n.
  pattern n.
  apply (wf_lt_induction_type).

  intros x IH.
  simple induction d1 ;  auto with coc.

 clear e A B s d1; intros ; clear H H0.
 generalize H1 ; clear H1.
   apply (coerces_db_dep (fun e1 T0 C0 s0 => fun d : (e1 |- T0 >>> C0 : s0) =>
     e1 = e -> T0 = Prod A' B' -> C0 = C -> s0 = s' ->     
     (x = depth (coerces_prod c t t0 c0 t1 t2) + depth d) ->
     e |- Prod A B >>> C0 : s')) ; intros ; auto with coc ; try discriminate.

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

  assert(e |- A'0 >>> A : s).
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

  assert(e |- Prod A B : Srt s').
  apply type_prod with s ; auto with coc.
  assert(e |- Prod A B >>> Prod A' B' : s').
  apply coerces_prod with s ; auto with coc.

  destruct c2.

  (* prod, conv_l < refl *) 
  apply coerces_conv_r with (Prod A' B') ; auto with coc.

  (* prod, conv_l < prod *)
  simpl in H4.
  induction (inv_conv_prod_sort_l t3 t4 c1).
  intuition.
  pose (unique_sort t7 H2).
  rewrite <- e1 in H1.
  pose (unique_sort H1 t).
  generalize dependent A'0.
  rewrite e2.
  intros.

  assert(e |- A'0 >>> A : s).
  pose (inv_conv_prod_l _ _ _ _ c1).
  pose(coerces_conv_l).
  rewrite e2 in t7.
  set (d := coerces_conv_l t10 t t0 (sym_conv _ _ c2) c).
  apply (IH (depth c2_1 + depth d)) with A1 c2_1 d ; auto with coc.
  simpl.
  rewrite H4 ; simpl.
  apply depth_prod_conv_prod.
  
  apply coerces_prod with s ; auto with coc core.

  cut(coerce_in_env (A' :: e) (A'0 :: e)) ; intros.
  assert(wf (A'0 :: e)).
  apply wf_var with s ; auto with coc.

  cut(A'0 :: e |- B' : Srt s') ; intros.
  cut(A'0 :: e |- B0 : Srt s') ; intros.
  pose (inv_conv_prod_r _ _ _ _ c1).
  set (d := coerces_conv_l H7 H8 t9 c2 c2_2).
  destruct (coerce_conv_env c0 H5 H6).
  apply (IH (depth c0 + depth d)) with B' x1 d ; auto with coc.
  simpl.
  rewrite H4.
  apply depth_prod_conv_prod2.

  apply (coerces_sort_l c2_2).
  apply (typ_conv_env t2 H5 H6).

  apply coerce_env_hd with s ; auto with coc core.
  apply coerces_conv_r with A1 ; auto with coc core.
  rewrite e2 in t7.
  apply t10.
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

 clear e A B s d1; intros ; clear H H0.
 generalize H1 ; clear H1.
 rename s0 into sum_sort0.
 rename s1 into sum_sort1.
   apply (coerces_db_dep (fun e1 T0 C0 s0 => fun d : (e1 |- T0 >>> C0 : s0) =>
     e1 = e -> T0 = Sum A' B' -> C0 = C -> s0 = s' ->     
     (x = depth (coerces_sum c t t0 c0 t1 t2 sum_sort0 sum_sort1) + depth d) ->
     e |- Sum A B >>> C0 : s')) ; intros ; auto with coc ; try discriminate.

  (* sum, refl *)
  rewrite H0 ;
  apply coerces_sum with s ; auto with coc.
  
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

  assert(e |- A >>> A'0 : s).
  apply (IH (depth c1 + depth c)) with A' c c1 ; auto.
  rewrite H5 ; simpl ; auto with coc arith.
  apply depth_prod_prod_l.
  auto with arith.

  cut(coerce_in_env (A' :: e) (A :: e)) ; intros.
  assert(wf (A :: e)).
  apply wf_var with s ; auto with coc.
  destruct (coerce_conv_env c2 H1 H7).
  
  apply coerces_sum with s ; auto with coc.
  
  apply (IH (depth c0 + depth x0)) with B' c0 x0 ; auto.
  rewrite e2.
  rewrite H5.
  simpl.
  apply depth_prod_prod_r.
  rewrite e1 ; auto.
  apply coerce_env_hd with s ; auto with coc.

  (* sum, subset *)
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
  rewrite <- H3 in sum_sort0 ; rewrite <- H3 in sum_sort1.
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

  assert(e |- Sum A B : Srt s').
  apply type_sum with s ; auto with coc.
  assert(e |- Sum A B >>> Sum A' B' : s').
  apply coerces_sum with s ; auto with coc.

  destruct c2.

  (* sum, conv_l < refl *) 
  apply coerces_conv_r with (Sum A' B') ; auto with coc.

  (* sum, conv_l < prod *)
  elim conv_prod_sum with A1 B0 A' B'; auto with coc.

  (* sum, conv_l < sum *)
  simpl in H4.
  induction (inv_conv_sum_sort_l t3 t4 c1).
  intuition.
  pose (unique_sort t7 H2).
  rewrite <- e1 in H1.
  pose (unique_sort H1 t).
  generalize dependent A'0.
  rewrite e2.
  intros.

  assert(e |- A >>> A'0 : s).
  pose (inv_conv_sum_l _ _ _ _ c1).
  pose(coerces_conv_l).
  rewrite e2 in t7.
  set (d := coerces_conv_l t t10 t6 c2 c2_1).
  apply (IH (depth d + depth c)) with A' c d ; auto with coc.
  simpl.
  rewrite H4 ; simpl.
  apply depth_sum_conv_sum.
  auto with arith.

  apply coerces_sum with s ; auto with coc core.

  cut(coerce_in_env (A1 :: e) (A :: e)) ; intros.
  assert(wf (A :: e)).
  apply wf_var with s ; auto with coc.

  cut(A :: e |- B' : Srt s') ; intros.
  cut(A :: e |- B0 : Srt s') ; intros.
  cut(A :: e |- B'0 : Srt s') ; intros.
  pose (inv_conv_sum_r _ _ _ _ c1).
  destruct (coerce_conv_env c2_2 H5 H6).
  set (d := coerces_conv_l H7 H8 H9 c2 x1).
  apply (IH (depth c0 + depth d)) with B' c0 d ; auto with coc.
  simpl.
  rewrite e3.
  rewrite H4.
  apply depth_prod_conv_prod2.

  pose (coerces_sort_r c2_2).
  apply (typ_conv_env t10 H5 H6).
  apply (typ_conv_env t8 H5 H6).
  apply (coerces_sort_r c0).

  apply coerce_env_hd with s ; auto with coc core.
  apply coerces_conv_r with A' ; auto with coc core.
  rewrite e2 in t7.
  apply t10.
  apply (inv_conv_sum_l _ _ _ _ c1).

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
  pose (coerces_conv_l t3 t7 t8 H1 c3).
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
   apply type_sum with s ; auto with coc.

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

  apply (coerces_db_dep (fun e1 T0 C0 s0 => fun d : (e1 |- T0 >>> C0 : s0) =>
     e1 = e -> T0 = Subset U' P -> C0 = C -> s0 = set ->     
     x = depth (coerces_sub_r c t) + depth d -> 
     e |- U >>> C : set))  ; intros ; auto with coc ; try discriminate.

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
  assert(e |- Prod A' B' : Srt s').
  apply type_prod with s ; auto with coc.
  destruct c ;
  pose (H1 := coerces_prod d2_1 t2 t3 d2_2 t4 t5) .
  (* conv_r < refl, prod *) 
  apply coerces_conv_l with (Prod A0 B0) ; auto with coc.

  (* conv_r < prod, prod *)
  simpl in H0.
  induction (inv_conv_prod_sort_l t0 t1 c0).
  intuition.
  pose (unique_sort t6 H2).
  pose (unique_sort t3 H3).
  generalize dependent A ; generalize dependent A'0.
  rewrite <- e1.
  intros.
  generalize dependent A' ; generalize dependent A0.
  generalize dependent c1 ; generalize dependent t7 ; rewrite e0.
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
  pose (coerces_conv_r (coerces_sort_l x1) (coerces_sort_r x1) (coerces_sort_l d2_2) x1 c4).
  
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
  assert(e |- Sum A' B' : Srt s').
  apply type_sum with s ; auto with coc.
  destruct c ;
  pose (H1 := coerces_sum d2_1 t2 t3 d2_2 t4 t5 s0 s1) .

  (* conv_r < refl, sum *) 
  apply coerces_conv_l with (Sum A0 B0) ; auto with coc.

  (* conv_r < prod, sum *)
  elim conv_prod_sum with A'0 B'0 A0 B0 ; auto with coc.

  (* conv_r < sum, sum *)
  simpl in H0.
  induction (inv_conv_sum_sort_l t0 t1 c0).
  intuition.
  pose (unique_sort t6 H2).
  pose (unique_sort t3 H3).
  generalize dependent A ; generalize dependent A'0.
  rewrite <- e1.
  intros.
  generalize dependent A' ; generalize dependent A0.
  generalize dependent c1 ; generalize dependent t7 ; rewrite e0.
  intros.
  clear e0 ; clear e1.

  pose (inv_conv_sum_l _ _ _ _ c0).
  pose (coerces_conv_r t7 H2 t3 c1 c).
  
  apply coerces_sum with s ; auto with coc core.

  apply (IH (depth c3 + depth d2_1)) with A0 c3 d2_1.
  rewrite H0 ; simpl.
  apply depth_conv_sum.
  auto.

  cut(coerce_in_env (A0 :: e) (A :: e)) ; intros.
  assert(wf (A :: e)).
  apply wf_var with s ; auto with coc.

  pose (inv_conv_sum_r _ _ _ _ c0).
  destruct (coerce_conv_env d2_2 H4 H5).
  pose (coerces_conv_l (coerces_sort_r c2) (coerces_sort_l x1)  (coerces_sort_r x1)  c4 x1).
  
  apply (IH (depth c2 + depth c5)) with B'0 c2 c5.
  rewrite H0 ; simpl.
  rewrite e0. apply depth_conv_sum2 .
  auto.
  apply coerce_env_hd with s ; auto with coc core.
  rewrite <- (unique_sort t6 H2).
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
  

  Focus 2.
  (* conv_r, sub_r *)
  apply coerces_sub_r ; auto with coc.
  pose (coerces_conv_r t t0 t1 c c0).
  apply (IH (depth c1 + depth d2)) with U c1 d2.
  rewrite H0 ; simpl ; try omega ; auto.
  auto.

  Focus 2.
  (* conv_r, conv_l *)
  assert (conv B B0).
  apply trans_conv_conv with A0 ; auto with coc.
  pose (coerces_conv_r t t0 t3 c H).
  apply (IH (depth c2 + depth d2)) with B0 c2 d2.
  rewrite H0 ; simpl ; try omega ; auto.
  auto.

  Focus 2.
   (* conv_r, conv_r *)
   apply coerces_conv_r with B0 ; auto with coc.
   apply coerces_conv_r with  ; auto with coc.

  assert (conv B B0).
  apply trans_conv_conv with A0 ; auto with coc.
  pose (coerces_conv_r t t0 t3 c H).
  apply (IH (depth c2 + depth d2)) with B0 c2 d2.
  rewrite H0 ; simpl ; try omega ; auto.
  auto.

  

  generalize dependent e.
  rewrite H2.

  rewrite 
  
  apply coerces_conv_l with U0.
  elim conv_subset_sum with U' P A0 B ; auto with coc.
  
  apply coerces_sub_r  ; auto with coc.
  apply coerces_conv_l with B ; auto with coc.

  generalize dependent s.
  generalize dependent c0.
  rewrite H1 ; rewrite H3 ; rewrite H2 ; intros.
  rewrite <- H4.
  (* sub_r, conv_r *)
  clear H0.
  simpl in H5.
  rewrite <- H2.
  rewrite <- H3.
  generalize dependent s.
  rewrite H1 ; intros.
  rewrite <- H4.
  apply coerces_conv_r with B ; auto with coc.

  apply coerces_refl ; auto .
  apply (coerces_sort_l c).
  
  (* sub_r, prod *)
  clear H0 H1.
  simpl in H6.
  rewrite <- H2.
  rewrite <- H3.
  rewrite <- H4.
  generalize dependent s' ; generalize dependent s.
  rewrite H2.
  intros.
  rewrite <- H5.
  apply coerces_prod with s ; auto with coc.

  (* sub_r, sum *)
  clear H0 H1.
  simpl in H6.
  rewrite <- H2.
  rewrite <- H3.
  rewrite <- H4.
  generalize dependent s' ; generalize dependent s.
  rewrite H2.
  intros.
  rewrite <- H5.
  apply coerces_sum with s ; auto with coc.

  (* sub_r, sub_l *)
  clear H0.
  simpl in H5.
  rewrite <- H2.
  rewrite <- H3.
  generalize dependent U0.
  rewrite H1 ; intros.
  apply coerces_sub_l ; auto with coc.

  (* sub_r, sub_r *)
  clear H0.
  simpl in H5.
  rewrite <- H2.
  rewrite <- H3.
  generalize dependent U'0.
  rewrite H1 ; intros.
  apply coerces_sub_r ; auto with coc.

  (* sub_r, conv_l *)
  clear H0.
  simpl in H5.
  rewrite <- H2.
  rewrite <- H3.
  generalize dependent s.
  rewrite H1 ; intros.
  rewrite <- H4.
  apply coerces_conv_l with B ; auto with coc.

  (* sub_r, conv_r *)
  clear H0.
  simpl in H5.
  rewrite <- H2.
  rewrite <- H3.
  generalize dependent s.
  rewrite H1 ; intros.
  rewrite <- H4.
  apply coerces_conv_r with B ; auto with coc.
  


apply coerces_sub_r ; auto with coc.
    apply (IH (depth c + depth d2)) with U' c d2.
    


pose (coerces_conv_l t3 t6 t7 c1 c2).
   


  generalize (depth c2_1) ;   generalize (depth c) ;   generalize (depth c0) ;   generalize (depth c2_2).
  
forall n0 n1 n2 n3, n3 + S n2 < S (max n2 n1 + S (S (max n3 n0)))
  generalize (depth c0) ;   generalize (depth c1) ;   generalize (depth c2) ;   generalize (depth c).


simple induction d2.
   generalize e0 A0 B0 A' B' s0 c t t0 s' c0 t1 t2 C d2 H1.
   clear e0 A0 B0 A' B' s0 c t t0 s' c0 t1 t2 C d2 H1.
   destruct d2.
   intros.
  
  set (T := Prod A' B').
  assert (T = Prod A' B').
  unfold T ; auto.
  
  intros C d2.
  cleainduction d2.
  rewrite H in d2 ; inversion d2 ; intros.

  (* Pi, Id *)
  rewrite <- H3 in d2.
  rewrite <- H3.
  apply coerces_prod with s ; auto with coc.
  
  (* Pi, Pi *)
  rewrite <- H8.
  apply coerces_prod with s ; auto with coc.
  

  
  

  generalize t2 ; clear t2.
  generalize t1 ; clear t1.
  generalize d1_2 ; clear d1_2.
  generalize s' ; clear s'.
  generalize t0 ; clear t0.
  generalize t ; clear t.
  generalize d1_1 ; clear d1_1.
  generalize s ; clear s.
  simpl.
  generalize A' B'.
  set (T := Prod A' B').
  assert (T = Prod A' B').
  unfold T ; auto.
  rewrite <- H1 in d2.
  
  induction d0 using coerces_db_dep.
  with (P :=
  fun e T C s => fun d : (e |- T >>>> C : s) =>
  forall d2 : e |- Prod A' B' >>>> C : s,
  build_pair (depth (coerces_prod d1_1 t t0 d1_2 t1 t2)) (depth d) = x ->
  e |- Prod A B >>>> C : s) ; simpl ; intros.

  elim d2 ; intros ; auto with coc.
  
  apply coerces_prod with s; auto with coc.
  
  
   rewrite H4  in d2.
  generalize H0 ; clear H0.

  generalize d2 ; clear d2.
  generalize e.
 ; generalize e ; generalize A' ; generalize B' ; generalize s'.
  Check coerces_db_rect.

  apply coerces_db_rect with

  (P:= 
  pattern d2.
  induction d2.
 ; intros ; auto with coc.
  

  induction d1 ; intros ; auto with coc.

  induction 1 ; simpl ; intros ; auto with coc.
Admitted.











Reserved Notation "G |- T >>> U : s" (at level 70, T, U, s at next level).

Parameter hnf : term -> term.
Parameter hnf_conv : forall T U, hnf T = U -> conv T U.
Definition is_hnf t := t = hnf t.

Parameter hnf_dec : forall t t', hnf t = t' ->
  (exists U, exists V, t' = Prod U V) \/
  (exists U, exists V, t' = Sum U V) \/
  (exists U, exists V, t' = Subset U V) \/
  (exists n, t' = Ref n) \/
  (exists M, exists N, t' = App M N /\ forall M' N', hnf M <> Abs M' N') \/
  (exists M, exists N, t' = Abs M N) \/
  (exists T, exists u, exists v, t' = Pair T u v) \/
  (exists M, t' = Pi1 M /\ forall T U V, hnf M <> Pair T U V) \/
  (exists M, t' = Pi2 M /\ forall T U V, hnf M <> Pair T U V).

Parameter hnf_def : forall t, exists t', hnf t = t'.
Parameter hnf_fun : forall t t' t'', hnf t = t' -> hnf t = t'' -> t' = t''.
  
Definition is_prod t := match t with Prod U V => True |  _ => False end.
Definition is_sum t := match t with Sum U V => True |  _ => False end.
Definition is_subset t := match t with Subset U V => True |  _ => False end.

Definition is_composite t := is_prod t \/ is_sum t \/ is_subset t.

Parameter is_composite_conv : forall e A B s,
  e |- A : Srt s -> e |- B : Srt s -> 
  is_composite A -> conv A B -> 
  is_composite (hnf B).

Parameter hnf_prod : forall U V, hnf (Prod U V ) = Prod U V.
Parameter hnf_sum : forall U V, hnf (Sum U V ) = Sum U V.
Parameter hnf_subset : forall U V, hnf (Subset U V ) = Subset U V.

Parameter conv_hnf_prod : forall e T T' s, 
  e |- T : Srt s -> e |- T' : Srt s -> 
  conv T T' -> forall U V, hnf T' = Prod U V ->
  exists U', exists V', hnf T = Prod U' V' /\ conv U U' /\ conv V V'.

Parameter conv_hnf_sum : forall e T T' s,
  e |- T : Srt s -> e |- T' : Srt s -> 
   conv T T' -> forall U V, hnf T' = Sum U V ->
  exists U', exists V', hnf T = Sum U' V' /\ conv U U' /\ conv V V'.

Parameter conv_hnf_subset : forall e T T' s,
  e |- T : Srt s -> e |- T' : Srt s -> 
   conv T T' -> forall U V, hnf T' = Subset U V ->
  exists U', exists V', hnf T = Subset U' V' /\ conv U U' /\ conv V V'.

Axiom generation_prod_conv : forall e A B A' B' s, 
  conv (Prod A B) (Prod A' B') ->
  e |- Prod A B : Srt s -> e |- Prod A' B' : Srt s ->
  (exists s', e |- A : Srt s' /\ e |- A' : Srt s') /\
  (A' :: e |- B : Srt s /\ A' :: e |- B' : Srt s).

Axiom generation_sum_conv : forall e A B A' B' s, 
  conv (Sum A B) (Sum A' B') ->
  e |- Sum A B : Srt s -> e |- Sum A' B' : Srt s ->
  (exists s', e |- A : Srt s' /\ e |- A' : Srt s') /\
  (A' :: e |- B : Srt s /\ A' :: e |- B' : Srt s).

Axiom generation_subset_conv : forall e A B A' B' s, 
  conv (Subset A B) (Subset A' B') ->
  e |- Subset A B : Srt s -> e |- Subset A' B' : Srt s ->
  (exists s', e |- A : Srt s' /\ e |- A' : Srt s') /\
  (A' :: e |- B : Srt s /\ A' :: e |- B' : Srt s).

Inductive coercea : env -> term -> term -> sort -> Set :=
  | coerce_conv : forall e A B s, e |- A : Srt s -> e |- B : Srt s ->
      is_hnf A -> is_hnf B -> ~ is_composite A ->  
      conv A B -> e |- A >>> B : s

  | coerce_prod : forall e A B A' B',
  forall s, e |- A' >>> A : s ->
  (* derivable *) e |- A' : Srt s -> e |- A : Srt s ->
  forall s', (A' :: e) |- B >>> B' : s' -> 
  (* derivable *) A :: e |- B : Srt s' -> A' :: e |- B' : Srt s' ->
  e |- (Prod A B) >>> (Prod A' B') : s'
  
  | coerce_sum : forall e A B A' B',
  forall s, e |- A >>> A' : s -> 
  (* derivable *) e |- A' : Srt s -> e |- A : Srt s ->
  forall s', (A :: e) |- B >>> B' : s' ->
  (* derivable *) A :: e |- B : Srt s' -> A' :: e |- B' : Srt s' ->
  sum_sort A B s s' -> sum_sort A' B' s s' ->
  e |- (Sum A B) >>> (Sum A' B') : s'

  | coerce_sub_l : forall e U P U', 
  e |- U >>> U' : set ->
  (* derivable *) U :: e |- P : Srt prop ->
  is_hnf U' ->
  e |- Subset U P >>> U' : set

  | coerce_sub_r : forall e U U' P,
  e |- U >>> U' : set -> 
  (* derivable *) U' :: e |- P : Srt prop ->
  is_hnf U ->
  e |- U >>> (Subset U' P) : set

  | coerce_hnf : forall e A B C D s,
  e |- A : Srt s -> e |- B : Srt s -> e |- C : Srt s -> e |- D : Srt s -> ~ (is_hnf A /\ is_hnf B) ->
  hnf A = B -> e |- B >>> C : s -> hnf D = C -> e |- A >>> D : s

where "G |- T >>> U : s" := (coercea G T U s).

Lemma eq_sort_dec : forall s s' : sort, { s = s' } + {s <> s'}.
Proof.
  double induction s s' ; intros ; try (solve [left ; auto with coc] ); try (right ; unfold not ; intros ; discriminate).
Qed.

Lemma eq_term_dec : forall t t' : term, { t = t' } + { t <> t' }.
Proof.
  double induction t t' ; intros ; try (solve [left ; auto with coc] ); try (right ; unfold not ; intros ; discriminate).
  destruct (eq_sort_dec s s0).
  left ; rewrite e ; auto.
  right. 
  unfold not ; intros.
  apply n.
  inversion H ; auto.
  
  destruct (eq_nat_dec n n0).
  left ; auto.
  right ; red in |- * ; intros ; apply n1.
  inversion H ; auto.

  destruct (H1 t1) ; destruct (H2 t0).
  left ; auto.
  rewrite e ; rewrite e0 ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.

  destruct (H1 t1).
  destruct (H2 t0).
  left ; auto.
  rewrite e ; rewrite e0 ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.

  destruct (H2 t2).
  destruct (H3 t1).
  destruct (H4 t0).
  left ; auto.
  rewrite e ; rewrite e0 ; rewrite e1 ;auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.

  destruct (H1 t1).
  destruct (H2 t0).
  left ; auto.
  rewrite e ; rewrite e0 ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.

  destruct (H1 t1).
  destruct (H2 t0).
  left ; auto.
  rewrite e ; rewrite e0 ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.

  destruct (H1 t1).
  destruct (H2 t0).
  left ; auto.
  rewrite e ; rewrite e0 ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.

  destruct (H0 t0).
  left ; auto.
  rewrite e; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.


  destruct (H0 t0).
  left ; auto.
  rewrite e; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.

  destruct (H1 t1).
  destruct (H2 t0).
  left ; auto.
  rewrite e ; rewrite e0 ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.
  right ; red in |- * ; intros Heq ; apply n ; inversion Heq ; auto.
Qed.

Check (coercea_ind).
Require Import Wellfounded.
Check lexprod_ind.

Require Import Coq.Arith.Max.

Fixpoint depth e T U s (d : coercea e T U s) { struct d } :  nat :=
  match d return nat with 
  coerce_conv _ _ _ _ _ _ _ _ _ _ => 1
  | coerce_prod e A B A' B' s HsubA HsA' HsA s' HsubB HsB HsB' =>
    S (max (depth HsubA) (depth HsubB))
  | coerce_sum e A B A' B' s HsubA HsA' HsA s' HsubB HsB HsB' sums sums' =>
    S (max (depth HsubA) (depth HsubB))
  | coerce_sub_l e U P U' HsubU Hsp hnfU' => S (depth HsubU)
  | coerce_sub_r e U U' P HsubU Hsp hnfU => S (depth HsubU)
  | coerce_hnf e A B C D s HsrtA HsrtB HsrtC HsrtD Hhnf hnfA HsubBC hnfD =>
    S (depth HsubBC)
 end.

Require Import Coq.Arith.Wf_nat.
Check well_founded_ltof.

Lemma wf_ltof_depth : forall e T U s, well_founded (ltof (e |- T >>> U : s) (depth (e:=e) (T:=T) (U:=U) (s:=s))).
Proof.
intros e T U s.
apply (well_founded_ltof (coercea e T U s) (@depth e T U s)).
Qed.


Lemma induction_depth : forall (P : forall e T U s, coercea e T U s -> Set),
       (forall e T U s, forall x : coercea e T U s, 
        (forall e' T' U' s', forall y : coercea e' T' U' s', ltof (e' |- T' >>> U' : s')
        (@depth e' T' U' s') y x -> P e' T' U' s' y) -> P e T U s x) ->
        forall e T U s, forall a : coercea e T U s, P e T U s a.

Check induction_ltof1.


Parameter coerce_lex_ind : 
  forall P : env -> term -> term -> sort -> 
  env -> term -> term -> sort -> Prop,
   (forall (e : env) A B s,
        e |- A : Srt s ->
        e |- B : Srt s ->
        is_hnf A -> is_hnf B -> ~ is_composite A -> conv A B -> P e A B s) ->
       (forall (e : env) A B A' B' s,
        e |- A' >>> A : s ->
        P e A' A s ->
        e |- A' : Srt s ->
        e |- A : Srt s ->
        forall s',
        A' :: e |- B >>> B' : s' ->
        P (A' :: e) B B' s' ->
        A :: e |- B : Srt s' ->
        A' :: e |- B' : Srt s' -> P e (Prod A B) (Prod A' B') s') ->
       (forall (e : env) A B A' B' s,
        e |- A >>> A' : s ->
        P e A A' s ->
        e |- A' : Srt s ->
        e |- A : Srt s ->
        forall s',
        A :: e |- B >>> B' : s' ->
        P (A :: e) B B' s' ->
        A :: e |- B : Srt s' ->
        A' :: e |- B' : Srt s' ->
        sum_sort A B s s' ->
        sum_sort A' B' s s' -> P e (Sum A B) (Sum A' B') s') ->
       (forall (e : env) (U P0 U' : term),
        e |- U >> U' : set ->
        U :: e |- P0 : Srt prop -> is_hnf U' -> P e (Subset U P0) U' set) ->
       (forall (e : env) (U U' P0 : term),
        e |- U >>> U' : set ->
        P e U U' set ->
        U' :: e |- P0 : Srt prop -> is_hnf U -> P e U (Subset U' P0) set) ->
       (forall (e : env) A B (C D : term) s,
        e |- A : Srt s ->
        e |- B : Srt s ->
        e |- C : Srt s ->
        e |- D : Srt s ->
        ~ (is_hnf A /\ is_hnf B) ->
        hnf A = B -> e |- B >>> C : s -> P e B C s -> hnf D = C -> P e A D s) ->
       forall (e : env) t t0 s, e |- t >>> t0 : s -> P e t t0 s


Theorem coerce_beta : forall e B C s, e |- B >>> C : s ->
  forall A D, e |- A : Srt s -> e |- B : Srt s -> e |- C : Srt s -> e |- D : Srt s ->
  is_hnf B -> is_hnf C -> conv A B -> conv C D ->
  e |- A >>> D : s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.

  destruct (eq_term_dec (hnf A0) A0).
  destruct (eq_term_dec (hnf D) D).
  
  apply coerce_conv ; try unfold is_hnf ; auto with coc.
  unfold not ; intros.
  apply H3 ; intros.
  rewrite H9.
  exact (is_composite_conv H5 H6 H13 H11).
  
  apply trans_conv_conv with A ; auto with coc.
  apply trans_conv_conv with B ; auto with coc.

  destruct (conv_hnf_prod H5 H6 H13 (hnf_prod A B)).
  destruct H15 ; intuition.
  rewrite <- H9 in H16.
  rewrite H16.
  destruct (conv_hnf_prod H8 H7 (sym_conv _ _ H14) (hnf_prod A' B')).
  destruct H17 ; intuition.
  rewrite <- H12 in H19.
  rewrite H19.

  rewrite H16 in H5.
  rewrite H19 in H8.
  rewrite H16 in H13.
  rewrite H19 in H14.

  destruct (generation_prod_conv H13 H5 H6).
  destruct (generation_prod_conv H14 H7 H8).
  destruct H20 ; destruct H23 ; intuition.

  rewrite <- (unique_sort H0 H22) in H28.
  rewrite <- (unique_sort H1 H26) in H25.
  clear H26 ; clear H22.

  apply coerce_prod with s ; auto with coc core.
  eapply IHcoercea1 ; auto with coc core.
  
Theorem coerce_trans : forall e A B C s, e |- A >>> B : s -> e |- B >>> C : s ->
  e |- A >>> C : s.
Proof.
  

Theorem coerce_trans : forall e A B C s, e |- A >> B : s -> e |- B >> C : s ->
  e |- A >> C : s.
Proof.
  induction 1 ; simpl ; intros ; auto with coc.
Admitted.
(*
  induction H2 ; simpl ; intros ; auto with coc.
  apply coerce_conv with A0 A0; auto.
  apply coerce_id ; auto.

  apply coerce_conv with (Prod A0 B) (Prod A' B'); auto with coc.
  apply type_prod with s ; auto with coc.
  apply type_prod with s ; auto with coc.

  apply coerce_prod with s ; auto with coc core.
  apply coerce_conv with e 

  apply coerce_id ; auto.

  

  apply coerce_prod with s ; auto with coc core.
*)