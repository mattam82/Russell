Require Import Lambda.Utils.
Require Import Lambda.Tactics.
Require Import Lambda.MyList.

Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.
Require Import Lambda.TPOSR.LiftSubst.
Require Import Lambda.TPOSR.Env.
Require Import Lambda.TPOSR.Types.
Require Import Lambda.TPOSR.Basic.
Require Import Lambda.TPOSR.Thinning.
Require Import Lambda.TPOSR.LeftReflexivity.
Require Import Lambda.TPOSR.Substitution.
Require Import Lambda.TPOSR.SubstitutionTPOSR.
Require Import Lambda.TPOSR.CtxConversion.
Require Import Lambda.TPOSR.RightReflexivity.
Require Import Lambda.TPOSR.UnicityOfSorting.
Require Import Lambda.TPOSR.CtxCoercion.
Require Import Lambda.TPOSR.Equiv.
Require Import Lambda.TPOSR.Generation.
Require Import Lambda.TPOSR.TypesDepth.
Require Import Lambda.TPOSR.Validity.
Require Import Lambda.TPOSR.TypesFunctionality.
Require Import Lambda.TPOSR.UniquenessOfTypes.
Require Import Lambda.TPOSR.ChurchRosserDepth.
Require Import Lambda.TPOSR.ChurchRosser.
Require Import Lambda.TPOSR.Injectivity.

Set Implicit Arguments.

Theorem subject_reduction_depth : forall t t', par_lred1 t t' -> forall e T, tposr_term_depth e t T ->
  tposr e t t' T.
Proof.
  unfold tposr_term_depth ; induction 1 ; simpl ; intros ; destruct_exists. 

  (* Beta *)
  pose (generation_app_depth H1) ; destruct_exists.
  assert(exists E, tposr_term_depth (T :: e) M E /\ e |-- Prod_l T E >-> Prod_l a Typ : b0).
  assert(e |-- (Prod_l a Typ) -> (Prod_l a Typ) : (Srt_l b0)).
  apply tposr_prod with c ; auto with coc.
  apply (refl_l (fromd H2)).
  apply (coerce_refl_l H4).

  destruct H8 ; destruct_exists.
  pose (generation_lambda_depth H8) ; destruct_exists.
  exists a5.
  split.
  exists a4 ; exists c1 ;auto.
  apply tposr_coerce_sym.
  pose (coerce_refl_l H19).
  rewrite (unique_sort H9 t).
  assumption.
  
  inversion H8.
  exists Typ.
  split.
  exists b2 ; exists c0.
  assumption.
  auto with coc.

  destruct_exists.
  pose (injectivity_of_pi_coerce H10).
  destruct_exists.
  apply tposr_conv with (lsubst N Typ) b0 ; auto with coc.
  pose (IHpar_lred1_1 _ _ H9).
  apply tposr_beta with T x2 Typ b0 ; auto with coc.
  apply (coerce_refl_r H11).
  apply tposr_coerce_env with (a :: e) ; auto with coc.
  apply (coerce_refl_l H4).
  apply coerce_env_hd with x2 ; auto with coc.
  apply tposr_conv with x1 b0 ; auto with coc.
  apply coerce_coerce_env with (a :: e) ; auto with coc.
  apply coerce_env_hd with x2 ; auto with coc.

  assert(tposr_term_depth e N a).
  exists a1 ; exists  b1 ; auto.
  pose (IHpar_lred1_2 _ _ H13).
  apply tposr_conv with a x2 ; auto with coc.

  (* Pi1_red *)
  pose (generation_pi1_depth H0) ; destruct_exists.
  destruct H5 ; destruct_exists.

  subst Typ.
  subst x.
  
  pose (generation_pair_depth H5) ; destruct_exists.
  subst T.
  subst a1.
  unfold equiv_sort in H16.
  assert(tposr_term_depth e M a2).
  exists a4 ; exists b4 ; auto.
  pose (IHpar_lred1 _ _ H1).
  pose (injectivity_of_sum_coerce H16) ; destruct_exists.
  assert(Heq:=unique_sort (coerce_refl_l H3) (coerce_refl_l H15)).
  subst a1.
  assert(Heq:=unique_sort (coerce_refl_l H4) (coerce_refl_l H17)).
  subst b6.
  assert(e |-- a0 >-> a2 : c) by (apply tposr_coerce_trans with a ; auto with coc).
  assert(a :: e |-- b0 >-> a3 : d) by (apply tposr_coerce_trans with b ; auto with coc).
  apply tposr_equiv_r with a ; auto with coc.
  assert(Heq:=unique_sort (coerce_refl_r H15) (fromd H6)). 
  subst c0.
  assert(a :: e |-- a3 -> b3 : c1).
  apply tposr_coerce_env with (a2 :: e) ; auto with coc.
  eauto with coc ecoc.
  apply coerce_env_hd with c ; auto with coc.
  assert(Heq:=unique_sort (coerce_refl_r H17) H21).
  subst c1.

  apply tposr_pi1_red with b2 c b3 d x a5 ; auto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_pair with c d x ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.

  inversion H5.
  subst b1 T a1 c0.
  subst Typ.
  pose (generation_pair_depth H10) ; destruct_exists.
  inversion H1.
  subst a1 a4.
  inversion H21.
  subst b1 b4 a5 a6.
  assert(tposr_term_depth e M a0).
  exists x ; exists b5 ; auto.
  pose (IHpar_lred1 _ _ H23).

  assert(Heq:=unique_sort (fromd H12) (fromd H6)).
  subst c0.
  assert(Heq:=unique_sort (fromd H8) (fromd H14)).
  subst c1.

  apply tposr_equiv_r with a ; auto with coc.
  apply tposr_pi1_red with a2 c a3 d x2 d0 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_pair with c d x2 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_coerce_sum with c d ; eauto with coc ecoc.

  (* Pi2_red *)
  pose (generation_pi2_depth H0) ; destruct_exists.
  destruct H5 ; destruct_exists.

  subst Typ.
  subst x.
  
  pose (generation_pair_depth H5) ; destruct_exists.
  subst T.
  subst a1.
  unfold equiv_sort in H16.
  assert(tposr_term_depth e N (lsubst M a3)).
  exists a5 ; exists b5 ; auto.
  pose (IHpar_lred1 _ _ H1).
  pose (injectivity_of_sum_coerce H16) ; destruct_exists.
  assert(Heq:=unique_sort (coerce_refl_l H3) (coerce_refl_l H15)).
  subst a1.
  assert(Heq:=unique_sort (coerce_refl_l H4) (coerce_refl_l H17)).
  subst b6.
  assert(e |-- a0 >-> a2 : c) by (apply tposr_coerce_trans with a ; auto with coc).
  assert(a :: e |-- b0 >-> a3 : d) by (apply tposr_coerce_trans with b ; auto with coc).
  apply tposr_equiv_r with (lsubst (Pi1_l (Sum_l a b) (Pair_l (Sum_l a2 a3) M N)) b) ; auto with coc.

  assert(Heq:=unique_sort (coerce_refl_r H15) (fromd H6)). 
  subst c0.
  assert(a :: e |-- a3 -> b3 : c1).
  apply tposr_coerce_env with (a2 :: e) ; auto with coc.
  eauto with coc ecoc.
  apply coerce_env_hd with c ; auto with coc.
  assert(Heq:=unique_sort (coerce_refl_r H17) H21).
  subst c1.

  apply tposr_pi2_red with b2 c b3 d x a4 ; auto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_pair with c d x ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.

  inversion H5.
  subst d0 T a1 c0.
  subst Typ.
  pose (generation_pair_depth H10) ; destruct_exists.
  inversion H1.
  subst a1 a4.
  inversion H21.
  subst b4 b5 a5 a6.
  assert(Heq:=unique_sort (fromd H12) (fromd H6)).
  subst c0.
  assert(Heq:=unique_sort (fromd H8) (fromd H14)).
  subst c1.

  assert (equiv e (lsubst M b0) (lsubst (Pi1_l (Sum_l a b) (Pair_l (Sum_l a0 b0) M N)) b)).
  right ; exists d.
  apply tposr_coerce_sym.
  apply substitution_tposr_coerce with a ; auto with coc.
  apply tposr_pi1_red with a2 c a3 d x2 x ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_pair with c d x2 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_coerce_sum with c d ; eauto with coc ecoc.

  assert(tposr_term_depth e N (lsubst M b0)).
  exists x ; exists b7 ; auto.
  pose (IHpar_lred1 _ _ H24).
  
  apply tposr_equiv_r with (lsubst (Pi1_l (Sum_l a b) (Pair_l (Sum_l a0 b0) M N)) b) ; auto with coc.
  apply tposr_pi2_red with a2 c a3 d x2 b1 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_pair with c d x2 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_coerce_sum with c d ; eauto with coc ecoc.

  (* Sort *)
  eauto with coc ecoc.

  (* Var *)
  eauto with coc ecoc.
  
  (* Abs *)
  pose (generation_lambda_depth H1) ; destruct_exists.
  subst x.
  assert(tposr_term_depth e T b) by eauto with coc ecoc.
  assert(tposr_term_depth (T :: e) M a1) by eauto with coc ecoc.
  pose (IHpar_lred1_1 _ _ H10).
  pose (IHpar_lred1_2 _ _ H8).
  apply tposr_conv with (Prod_l T a1) b0 ; auto with coc.
  apply tposr_abs with b b1 b0 ; eauto with coc ecoc.

  (* App *)
  pose (generation_app_depth H2) ; destruct_exists.
  apply tposr_conv with (lsubst N T) b0 ; auto with coc.
  assert(tposr_term_depth (a :: e) T b0) by eauto with coc ecoc.
  assert(tposr_term_depth e N a) by eauto with coc ecoc.
  pose (IHpar_lred1_1 _ _ H10).
  pose (IHpar_lred1_3 _ _ H11).
  destruct H9 ; destruct_exists.

  assert(tposr_term_depth e M (Prod_l a T)) by eauto with coc ecoc.
  pose (IHpar_lred1_2 _ _ H14).
  apply tposr_app with a b c b0  ; eauto with coc ecoc.

  assert(e |-- M -> M : Prod_l a T).
  subst M.
  apply tposr_abs with c T b0 ; auto with coc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  assert(tposr_term_depth e M (Prod_l a T)).
  destruct (tod H15).
  exists M ; exists x1 ; eauto with coc ecoc.
  pose (IHpar_lred1_2 _ _ H16).
  apply tposr_app with a b c b0  ; eauto with coc ecoc.

  (* Pair *)
  pose (generation_pair_depth H2) ; destruct_exists.
  assert(e |-- Sum_l a a0 -> Sum_l a a0 : x1).
  apply tposr_sum with c c0 ; eauto with coc ecoc.
  assert(tposr_term_depth e T x1).
  destruct (tod H15).
  exists T ; exists x2 ; subst T ; auto.
  assert(tposr_term_depth e M a) by eauto with coc ecoc.
  assert(tposr_term_depth e N (lsubst M a0)) by eauto with coc ecoc.
  pose (IHpar_lred1_1 _ _ H16).
  pose (IHpar_lred1_2 _ _ H17).
  pose (IHpar_lred1_3 _ _ H18).
  apply tposr_conv with (Sum_l a a0) x1 ; auto with coc ecoc.
  subst T.
  subst x.
  pose (generation_sum t) ; destruct_exists.
  subst T'.
  apply tposr_pair with c c0 x1 ; auto with coc.
  rewrite (unique_sort (fromd H4) H3) ; auto.
  rewrite (unique_sort (fromd H6) H13) ; auto.

  (* Prod *)
  pose (generation_prod_depth H1) ; destruct_exists.
  subst x.
  assert(tposr_term_depth e M b) by eauto with coc ecoc.
  assert(tposr_term_depth (M :: e) N b0) by eauto with coc ecoc.
  pose (IHpar_lred1_1 _ _ H6).
  pose (IHpar_lred1_2 _ _ H8).
  apply tposr_equiv_l with b0  ; auto with coc ecoc.
  apply tposr_prod with b ; auto with coc.

  (* Sum *)
  pose (generation_sum_depth H1) ; destruct_exists.
  subst x.
  assert(tposr_term_depth e M b) by eauto with coc ecoc.
  assert(tposr_term_depth (M :: e) N b0) by eauto with coc ecoc.
  pose (IHpar_lred1_1 _ _ H7).
  pose (IHpar_lred1_2 _ _ H9).
  apply tposr_equiv_l with x1 ; auto with coc ecoc.
  apply tposr_sum with b b0 ; auto with coc.

  (* Subset *)
  pose (generation_subset_depth H1) ; destruct_exists.
  subst x.
  assert(tposr_term_depth e M set) by eauto with coc ecoc.
  assert(tposr_term_depth (M :: e) N prop) by eauto with coc ecoc.
  pose (IHpar_lred1_1 _ _ H6).
  pose (IHpar_lred1_2 _ _ H8).
  apply tposr_conv with set kind ; auto with coc ecoc.
  
  (* Pi1 *)
  pose (generation_pi1_depth H1) ; destruct_exists.
  destruct H6 ; destruct_exists.

  subst x.
  destruct (validity (fromd H6)) ; destruct_exists ; try discriminate.
  assert(tposr_term_depth e T b2) by (subst T ; eauto with coc ecoc).
  assert(tposr_term_depth e M (Sum_l a b)) by eauto with coc ecoc.
  pose (IHpar_lred1_1 _ _ H8).
  pose (IHpar_lred1_2 _ _ H9).
  apply tposr_equiv_l with a ; auto with coc.
  subst T.
  pose (generation_sum t) ; destruct_exists.
  subst T'.
  assert(Heq:=unique_sort (coerce_refl_l H4) H2).
  subst b3.
  assert(Heq:=unique_sort (coerce_refl_l H5) H10).
  subst b4.
  apply tposr_pi1 with c d x ; eauto with coc ecoc.

  subst x.
  destruct (validity (fromd H11)) ; destruct_exists ; try discriminate.
  pose (generation_sum H13) ; destruct_exists.
  subst a4.
  assert(Heq:=unique_sort (coerce_refl_r H4) H14).
  subst b5.
  assert(a :: e |-- b0 -> a6 : b6).
  apply tposr_coerce_env with (a0 :: e) ; auto with coc.
  apply coerce_env_hd with c ; eauto with coc ecoc.
  assert(Heq:=unique_sort (coerce_refl_r H5) H17).
  subst b6.

  assert(e |-- Sum_l a b -> Sum_l a b : x).
  apply tposr_sum with c d ; eauto with coc ecoc.
  
  assert(tposr_term_depth e T x).
  subst T ; eauto with coc ecoc.
  assert(tposr_term_depth e M (Sum_l a0 b0)) by eauto with coc ecoc.
  pose (IHpar_lred1_1 _ _ H20).
  pose (IHpar_lred1_2 _ _ H21).
  apply tposr_equiv_l with a ; auto with coc.
  subst T.
  pose (generation_sum t) ; destruct_exists.
  subst T'.
  assert(Heq:=unique_sort (coerce_refl_l H4) H2).
  subst b5.
  assert(Heq:=unique_sort (coerce_refl_l H5) H22).
  subst b6.
  apply tposr_pi1 with c d x ; auto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_conv with (Sum_l a0 b0) x ; auto with coc.
  assert(coerce_in_env (a :: e) (a0 :: e)).
  apply coerce_env_hd with c ; auto with coc ecoc.
  apply tposr_coerce_sum with c d ; auto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply coerce_coerce_env with (a :: e) ; auto with coc.
  apply tposr_coerce_env with (a :: e) ; eauto with coc ecoc.
  eauto with coc ecoc.

  (* Pi2 *)
  pose (generation_pi2_depth H1) ; destruct_exists.
  destruct H6 ; destruct_exists.

  subst x.
  destruct (validity (fromd H6)) ; destruct_exists ; try discriminate.
  assert(tposr_term_depth e T b2) by (subst T ; eauto with coc ecoc).
  assert(tposr_term_depth e M (Sum_l a b)) by eauto with coc ecoc.
  pose (IHpar_lred1_1 _ _ H8).
  pose (IHpar_lred1_2 _ _ H9).
  apply tposr_equiv_l with (lsubst (Pi1_l T M) b) ; auto with coc.
  subst T.
  pose (generation_sum t) ; destruct_exists.
  subst T'.
  assert(Heq:=unique_sort (coerce_refl_l H4) H2).
  subst b3.
  assert(Heq:=unique_sort (coerce_refl_l H5) H10).
  subst b4.
  apply tposr_pi2 with c d x ; eauto with coc ecoc.

  subst x.
  destruct (validity (fromd H11)) ; destruct_exists ; try discriminate.
  pose (generation_sum H13) ; destruct_exists.
  subst a4.
  assert(Heq:=unique_sort (coerce_refl_r H4) H14).
  subst b5.
  assert(a :: e |-- b0 -> a6 : b6).
  apply tposr_coerce_env with (a0 :: e) ; auto with coc.
  apply coerce_env_hd with c ; eauto with coc ecoc.
  assert(Heq:=unique_sort (coerce_refl_r H5) H17).
  subst b6.

  assert(e |-- Sum_l a b -> Sum_l a b : x).
  apply tposr_sum with c d ; eauto with coc ecoc.
  
  assert(tposr_term_depth e T x).
  subst T ; eauto with coc ecoc.
  assert(tposr_term_depth e M (Sum_l a0 b0)) by eauto with coc ecoc.
  pose (IHpar_lred1_1 _ _ H20).
  pose (IHpar_lred1_2 _ _ H21).
  apply tposr_equiv_l with (lsubst (Pi1_l T M) b) ; auto with coc.
  subst T.
  pose (generation_sum t) ; destruct_exists.
  subst T'.
  assert(Heq:=unique_sort (coerce_refl_l H4) H2).
  subst b5.
  assert(Heq:=unique_sort (coerce_refl_l H5) H22).
  subst b6.

  apply tposr_pi2 with c d x ; auto with coc ecoc.
  eauto with coc ecoc.
  apply tposr_conv with (Sum_l a0 b0) x ; auto with coc.
  assert(coerce_in_env (a :: e) (a0 :: e)).
  apply coerce_env_hd with c ; auto with coc ecoc.
  apply tposr_coerce_sum with c d ; auto with coc ecoc.
  eauto with coc ecoc.
  eauto with coc ecoc.
  apply coerce_coerce_env with (a :: e) ; auto with coc.
  apply tposr_coerce_env with (a :: e) ; eauto with coc ecoc.
  eauto with coc ecoc.
Qed.

Corollary subject_reduction : forall t t', par_lred1 t t' -> forall e T, tposr_term e t T ->
  e |-- t -> t' : T.
Proof.
  intros.
  apply subject_reduction_depth ; eauto with coc ecoc.
Qed.



Corollary subject_reduction_p : forall t t', par_lred t t' -> 
  forall e T, tposr_term e t T ->
  tposrp e t t' T.
Proof.
  induction 1.
  intros.
  apply tposrp_tposr.
  apply (subject_reduction H H0).
  intros.
  pose (IHclos_trans1 _ _ H1).
  pose (tposrp_refl_r t).
  assert(tposr_term e y T).
  exists y ; auto.
  pose (IHclos_trans2 _ _ H2).
  apply tposrp_trans with y ; auto.
Qed.
