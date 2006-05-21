Require Import TPOSR.Terms.
Require Import TPOSR.LiftSubst.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.

Inductive lred1 : lterm -> lterm -> Prop :=
| beta : forall T1 M N T, lred1 (App_l T1 (Abs_l T M) N) (lsubst N M)
| pi1 : forall T M N, lred1 (Pi1_l (Pair_l T M N)) M
| pi2 : forall T M N, lred1 (Pi2_l (Pair_l T M N)) N
| abs_lred_l : forall M M', lred1 M M' -> forall N, lred1 (Abs_l M N) (Abs_l M' N)
| abs_lred_r : forall M M', lred1 M M' -> forall N, lred1 (Abs_l N M) (Abs_l N M')
| app_lred_T :
forall T S, lred1 T S -> forall M1 M2, lred1 (App_l T M1 M2) (App_l S M1 M2)
| app_lred_l : forall M1 N1, lred1 M1 N1 -> forall T1 M2, lred1 (App_l T1 M1 M2) (App_l T1 N1 M2)
| app_lred_r :
forall M2 N2, lred1 M2 N2 -> forall T1 M1, lred1 (App_l T1 M1 M2) (App_l T1 M1 N2)
| pair_lred_T :
forall T S, lred1 T S -> forall M1 M2, lred1 (Pair_l T M1 M2) (Pair_l S M1 M2)
| pair_lred_l :
forall M1 N1, lred1 M1 N1 -> forall T M2, lred1 (Pair_l T M1 M2) (Pair_l T N1 M2)
| pair_lred_r :
forall M2 N2, lred1 M2 N2 -> forall T M1, lred1 (Pair_l T M1 M2) (Pair_l T M1 N2)
| prod_lred_l :
forall M1 N1, lred1 M1 N1 -> forall M2, lred1 (Prod_l M1 M2) (Prod_l N1 M2)
| prod_lred_r :
forall M2 N2, lred1 M2 N2 -> forall M1, lred1 (Prod_l M1 M2) (Prod_l M1 N2)
| sum_lred_l :
forall M1 N1, lred1 M1 N1 -> forall M2, lred1 (Sum_l M1 M2) (Sum_l N1 M2)
    | sum_lred_r :
        forall M2 N2, lred1 M2 N2 -> forall M1, lred1 (Sum_l M1 M2) (Sum_l M1 N2)
    | subset_lred_l :
        forall M1 N1, lred1 M1 N1 -> forall M2, lred1 (Subset_l M1 M2) (Subset_l N1 M2)
    | subset_lred_r :
        forall M2 N2, lred1 M2 N2 -> forall M1, lred1 (Subset_l M1 M2) (Subset_l M1 N2)
    | pi1_lred :
        forall M N, lred1 M N -> lred1 (Pi1_l M) (Pi1_l N)
    | pi2_lred :
        forall M N, lred1 M N -> lred1 (Pi2_l M) (Pi2_l N)
    | let_in_lred_l :
        forall M1 N1, lred1 M1 N1 -> forall M2, lred1 (Let_in_l M1 M2) (Let_in_l N1 M2)
    | let_in_lred_r :
        forall M2 N2, lred1 M2 N2 -> forall M1, lred1 (Let_in_l M1 M2) (Let_in_l M1 N2).
      
  Inductive lred M : lterm -> Prop :=
    | refl_lred : lred M M
    | trans_lred : forall (P : lterm) N, lred M P -> lred1 P N -> lred M N.

  Inductive conv M : lterm -> Prop :=
    | refl_conv : conv M M
    | trans_conv_lred : forall (P : lterm) N, conv M P -> lred1 P N -> conv M N
    | trans_conv_exp : forall (P : lterm) N, conv M P -> lred1 N P -> conv M N.

  Inductive par_lred1 : lterm -> lterm -> Prop :=
    | par_beta :
        forall Typ, 
        forall M M',
        par_lred1 M M' ->
        forall N N',
        par_lred1 N N' -> forall T, par_lred1 (App_l Typ (Abs_l T M) N) (lsubst N' M')
    | par_pi1 : forall M M', par_lred1 M M' -> 
      forall T N, par_lred1 (Pi1_l (Pair_l T M N)) M'
    | par_pi2 : forall N N', par_lred1 N N' -> forall T M,
      par_lred1 (Pi2_l (Pair_l T M N)) N'
    | sort_par_lred : forall s, par_lred1 (Srt_l s) (Srt_l s)
    | ref_par_lred : forall n, par_lred1 (Ref_l n) (Ref_l n)
    | abs_par_lred :
        forall M M',
        par_lred1 M M' ->
        forall T T', par_lred1 T T' -> par_lred1 (Abs_l T M) (Abs_l T' M')
    | app_par_lred :forall T T', par_lred1 T T' ->
        forall M M',
        par_lred1 M M' ->
        forall N N', par_lred1 N N' -> par_lred1 (App_l T M N) (App_l T' M' N')
    | pair_par_lred : forall T T', par_lred1 T T' ->
        forall M M',
        par_lred1 M M' ->
        forall N N', par_lred1 N N' -> par_lred1 (Pair_l T M N) (Pair_l T' M' N')
    | prod_par_lred :
        forall M M',
        par_lred1 M M' ->
        forall N N', par_lred1 N N' -> par_lred1 (Prod_l M N) (Prod_l M' N')
    | sum_par_lred :
        forall M M',
        par_lred1 M M' ->
        forall N N', par_lred1 N N' -> par_lred1 (Sum_l M N) (Sum_l M' N')
    | subset_par_lred :
        forall M M',
        par_lred1 M M' ->
        forall N N', par_lred1 N N' -> par_lred1 (Subset_l M N) (Subset_l M' N')
    | pi1_par_lred :
        forall M M', par_lred1 M M' -> par_lred1 (Pi1_l M) (Pi1_l M')
    | pi2_par_lred :
        forall M M', par_lred1 M M' -> par_lred1 (Pi2_l M) (Pi2_l M')
    | let_in_par_lred :
        forall M M',
        par_lred1 M M' ->
        forall N N', par_lred1 N N' -> par_lred1 (Let_in_l M N) (Let_in_l M' N').

  Definition par_lred := clos_trans lterm par_lred1.

  Hint Resolve beta pi1 pi2 abs_lred_l abs_lred_r app_lred_T app_lred_l app_lred_r pair_lred_T pair_lred_l pair_lred_r : coc.
  Hint Resolve prod_lred_l prod_lred_r sum_lred_l sum_lred_r subset_lred_l subset_lred_r pi1_lred pi2_lred let_in_lred_l let_in_lred_r : coc.
  Hint Resolve refl_lred refl_conv: coc.
  Hint Resolve par_beta par_pi1 par_pi2 sort_par_lred ref_par_lred abs_par_lred app_par_lred pair_par_lred
    prod_par_lred sum_par_lred subset_par_lred pi1_par_lred pi2_par_lred let_in_par_lred: coc.

  Hint Unfold par_lred: coc.


Section Normalisation_Forte.

  Definition normal t : Prop := forall u, ~ lred1 t u.

  Definition sn : lterm -> Prop := Acc (transp _ lred1).

End Normalisation_Forte.

  Hint Unfold sn: coc.



  Lemma one_step_lred : forall M N, lred1 M N -> lred M N.
intros.
apply trans_lred with M; auto with coc core arith sets.
Qed.

  Hint Resolve one_step_lred: coc.


  Lemma lred1_lred_ind :
   forall N (P : lterm -> Prop),
   P N ->
   (forall M (R : lterm), lred1 M R -> lred R N -> P R -> P M) ->
   forall M, lred M N -> P M.
cut
 (forall M N,
  lred M N ->
  forall P : lterm -> Prop,
  P N -> (forall M (R : lterm), lred1 M R -> lred R N -> P R -> P M) -> P M).
intros.
apply (H M N); auto with coc core arith sets.

simple induction 1; intros; auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply H4 with N0; auto with coc core arith sets.

intros.
apply H4 with R; auto with coc core arith sets.
apply trans_lred with P; auto with coc core arith sets.
Qed.


  Lemma trans_lred_lred : forall M N (P : lterm), lred M N -> lred N P -> lred M P.
intros.
generalize H0 M H.
simple induction 1; auto with coc core arith sets.
intros.
apply trans_lred with P0; auto with coc core arith sets.
Qed.
 

  Lemma lred_lred_app :
   forall T T0 u u0 v v0, lred T T0 -> lred u u0 -> lred v v0 -> lred (App_l T u v) (App_l T0 u0 v0).
simple induction 1.
simple induction 1; 
simple induction 1 ; intros; auto with coc core arith sets.
apply trans_lred with (App_l T u P); auto with coc core arith sets.
pose (H2 H4).
apply trans_lred with (App_l T u v0); auto with coc core arith sets.

pose (H5 H7).
apply trans_lred with (App_l T N0 v0); auto with coc core arith sets.

intros.
pose (H1 H3 H4).
apply trans_lred with (App_l P u0 v0); auto with coc core arith sets.
Qed.

Lemma lred_lred_pair :
   forall T T0 u u0 v v0, lred T T0 -> lred u u0 -> lred v v0 -> lred (Pair_l T u v) (Pair_l T0 u0 v0).
simple induction 1.
simple induction 1.
simple induction 1 ; intros ; auto with coc core arith sets.
apply trans_lred with (Pair_l T u P); auto with coc core arith sets.

induction 4 ; intros ; auto with coc core arith sets.
apply trans_lred with (Pair_l T P v); auto with coc core arith sets.
apply trans_lred with (Pair_l T P N0); auto with coc core arith sets.
apply H2 ; auto with coc core arith sets.
apply trans_lred with P0 ; auto.

induction 4.
induction 1 ; intros ; auto with coc core arith sets.
apply trans_lred with (Pair_l P u v); auto with coc core arith sets.
apply trans_lred with (Pair_l P u N0); auto with coc core arith sets.
apply H1 ; auto with coc core arith sets.
apply trans_lred with P0; auto with coc core arith sets.

induction 1 ; intros ; auto with coc core arith sets.
apply trans_lred with (Pair_l P N0 v); auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply trans_lred with P0; auto with coc core arith sets.
apply trans_lred with (Pair_l P N0 N1); auto with coc core arith sets.
apply H1 ; auto with coc core arith sets.
apply trans_lred with P0; auto with coc core arith sets.
apply trans_lred with P1; auto with coc core arith sets.
Qed.

Ltac lred_lred_tac t :=
  intros u ; elim u ; 
  [ (intros u0 ; elim u0; intros v v0 P; auto with coc core arith sets ;
     apply trans_lred with (t u P); auto with coc core arith sets) 
  | intros v v0 P ; apply trans_lred with (t P v0); auto with coc core arith sets ].

Lemma lred_lred_abs :
   forall u u0 v v0, lred u u0 -> lred v v0 -> lred (Abs_l u v) (Abs_l u0 v0).
Proof.
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_lred with (Abs_l u P); auto with coc core arith sets.

intros.
apply trans_lred with (Abs_l P v0); auto with coc core arith sets.
Qed.


  Lemma lred_lred_prod :
   forall u u0 v v0, lred u u0 -> lred v v0 -> lred (Prod_l u v) (Prod_l u0 v0).
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_lred with (Prod_l u P); auto with coc core arith sets.

intros.
apply trans_lred with (Prod_l P v0); auto with coc core arith sets.
Qed.

  Lemma lred_lred_sum :
   forall u u0 v v0, lred u u0 -> lred v v0 -> lred (Sum_l u v) (Sum_l u0 v0).
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_lred with (Sum_l u P); auto with coc core arith sets.

intros.
apply trans_lred with (Sum_l P v0); auto with coc core arith sets.
Qed.

  Lemma lred_lred_subset :
   forall u u0 v v0, lred u u0 -> lred v v0 -> lred (Subset_l u v) (Subset_l u0 v0).
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_lred with (Subset_l u P); auto with coc core arith sets.

intros.
apply trans_lred with (Subset_l P v0); auto with coc core arith sets.
Qed.

  Lemma lred_lred_pi1 : forall u u0, lred u u0 -> lred (Pi1_l u) (Pi1_l u0).
simple induction 1 ; auto with coc core arith sets.
intros.
apply trans_lred with (Pi1_l P); auto with coc core arith sets.
Qed.

  Lemma lred_lred_pi2 : forall u u0, lred u u0 -> lred (Pi2_l u) (Pi2_l u0).
simple induction 1 ; auto with coc core arith sets.
intros.
apply trans_lred with (Pi2_l P); auto with coc core arith sets.
Qed.

  Lemma lred_lred_let_in :
   forall u u0 v v0, lred u u0 -> lred v v0 -> lred (Let_in_l u v) (Let_in_l u0 v0).
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_lred with (Let_in_l u P); auto with coc core arith sets.

intros.
apply trans_lred with (Let_in_l P v0); auto with coc core arith sets.
Qed.

  Hint Resolve lred_lred_app lred_lred_abs lred_lred_prod: coc.
  Hint Resolve lred_lred_pair lred_lred_sum lred_lred_subset lred_lred_let_in lred_lred_pi1 lred_lred_pi2 : coc.


  Lemma lred1_llift :
   forall u v, lred1 u v -> forall n k, lred1 (llift_rec n u k) (llift_rec n v k).
simple induction 1; simpl in |- *; intros; auto with coc core arith sets.
rewrite distr_llift_lsubst; auto with coc core arith sets.
Qed.

  Hint Resolve lred1_llift: coc.


  Lemma lred1_lsubst_r :
   forall t u,
   lred1 t u -> forall (a : lterm) k, lred1 (lsubst_rec a t k) (lsubst_rec a u k).
simple induction 1; simpl in |- *; intros; auto with coc core arith sets.
rewrite distr_lsubst; auto with coc core arith sets.
Qed.


  Lemma lred1_lsubst_l :
   forall (a : lterm) t u k,
   lred1 t u -> lred (lsubst_rec t a k) (lsubst_rec u a k).
simple induction a; simpl in |- *; auto with coc core arith sets.
intros.
elim (lt_eq_lt_dec k n);
 [ intro a0 | intro b; auto with coc core arith sets ].
elim a0; auto with coc core arith sets.
unfold llift in |- *; auto with coc core arith sets.
Qed.

  Hint Resolve lred1_lsubst_l lred1_lsubst_r: coc.


  Lemma lred_prod_prod :
   forall u v t,
   lred (Prod_l u v) t ->
   forall P : Prop,
   (forall a b : lterm, t = Prod_l a b -> lred u a -> lred v b -> P) -> P.
simple induction 1; intros.
apply H0 with u v; auto with coc core arith sets.

apply H1; intros.
inversion_clear H4 in H2.
inversion H2.
apply H3 with N1 b; auto with coc core arith sets.
apply trans_lred with a; auto with coc core arith sets.

apply H3 with a N2; auto with coc core arith sets.
apply trans_lred with b; auto with coc core arith sets.
Qed.


  Lemma lred_sum_sum :
   forall u v t,
   lred (Sum_l u v) t ->
   forall P : Prop,
   (forall a b : lterm, t = Sum_l a b -> lred u a -> lred v b -> P) -> P.
simple induction 1; intros.
apply H0 with u v; auto with coc core arith sets.

apply H1; intros.
inversion_clear H4 in H2.
inversion H2.
apply H3 with N1 b; auto with coc core arith sets.
apply trans_lred with a; auto with coc core arith sets.

apply H3 with a N2; auto with coc core arith sets.
apply trans_lred with b; auto with coc core arith sets.
Qed.

  Lemma lred_subset_subset :
   forall u v t,
   lred (Subset_l u v) t ->
   forall P : Prop,
   (forall a b : lterm, t = Subset_l a b -> lred u a -> lred v b -> P) -> P.
simple induction 1; intros.
apply H0 with u v; auto with coc core arith sets.

apply H1; intros.
inversion_clear H4 in H2.
inversion H2.
apply H3 with N1 b; auto with coc core arith sets.
apply trans_lred with a; auto with coc core arith sets.

apply H3 with a N2; auto with coc core arith sets.
apply trans_lred with b; auto with coc core arith sets.
Qed.

  Lemma lred_sort_sort : forall s t, lred (Srt_l s) t -> t <> Srt_l s -> False.
simple induction 1; intros; auto with coc core arith sets.
apply H1.
generalize H2.
case P; intros; try discriminate.
inversion_clear H4.
Qed.

  Lemma lred_ref_ref : forall n t, lred (Ref_l n) t -> t <> Ref_l n -> False.
simple induction 1; intros; auto with coc core arith sets.
apply H1.
generalize H2.
case P; intros; try discriminate.
inversion_clear H4.
Qed.


  Lemma one_step_conv_exp : forall M N, lred1 M N -> conv N M.
intros.
apply trans_conv_exp with N; auto with coc core arith sets.
Qed.


  Lemma lred_conv : forall M N, lred M N -> conv M N.
simple induction 1; auto with coc core arith sets.
intros; apply trans_conv_lred with P; auto with coc core arith sets.
Qed.

  Hint Resolve one_step_conv_exp lred_conv: coc.


  Lemma sym_conv : forall M N, conv M N -> conv N M.
simple induction 1; auto with coc core arith sets.
simple induction 2; intros; auto with coc core arith sets.
apply trans_conv_lred with P0; auto with coc core arith sets.

apply trans_conv_exp with P0; auto with coc core arith sets.

simple induction 2; intros; auto with coc core arith sets.
apply trans_conv_lred with P0; auto with coc core arith sets.

apply trans_conv_exp with P0; auto with coc core arith sets.
Qed.

  Hint Immediate sym_conv: coc.


  Lemma trans_conv_conv :
   forall M N (P : lterm), conv M N -> conv N P -> conv M P.
intros.
generalize M H; elim H0; intros; auto with coc core arith sets.
apply trans_conv_lred with P0; auto with coc core arith sets.

apply trans_conv_exp with P0; auto with coc core arith sets.
Qed.


  Lemma conv_conv_prod :
   forall a b c d : lterm, conv a b -> conv c d -> conv (Prod_l a c) (Prod_l b d).
intros.
apply trans_conv_conv with (Prod_l a d).
elim H0; intros; auto with coc core arith sets.
apply trans_conv_lred with (Prod_l a P); auto with coc core arith sets.

apply trans_conv_exp with (Prod_l a P); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_lred with (Prod_l P d); auto with coc core arith sets.

apply trans_conv_exp with (Prod_l P d); auto with coc core arith sets.
Qed.


Lemma conv_conv_sum : forall a b c d : lterm, conv a b -> conv c d -> conv (Sum_l a c) (Sum_l b d).
Proof.
intros.
apply trans_conv_conv with (Sum_l a d).
elim H0; intros; auto with coc core arith sets.
apply trans_conv_lred with (Sum_l a P); auto with coc core arith sets.

apply trans_conv_exp with (Sum_l a P); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_lred with (Sum_l P d); auto with coc core arith sets.

apply trans_conv_exp with (Sum_l P d); auto with coc core arith sets.
Qed.


Lemma conv_conv_subset : 
  forall a b c d : lterm, conv a b -> conv c d -> conv (Subset_l a c) (Subset_l b d).
Proof.
intros.
apply trans_conv_conv with (Subset_l a d).
elim H0; intros; auto with coc core arith sets.
apply trans_conv_lred with (Subset_l a P); auto with coc core arith sets.

apply trans_conv_exp with (Subset_l a P); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_lred with (Subset_l P d); auto with coc core arith sets.

apply trans_conv_exp with (Subset_l P d); auto with coc core arith sets.
Qed.

Lemma conv_conv_pair : forall T S a b c d : lterm, conv T S -> conv a b -> conv c d -> conv (Pair_l T a c) (Pair_l S b d).
Proof.
intros.
apply trans_conv_conv with (Pair_l T a d).
elim H1; intros; auto with coc core arith sets.
apply trans_conv_lred with (Pair_l T a P); auto with coc core arith sets.

apply trans_conv_exp with (Pair_l T a P); auto with coc core arith sets.

apply trans_conv_conv with (Pair_l T b d); auto with coc core arith sets.
elim H0; intros; auto with coc core arith sets.
apply trans_conv_lred with (Pair_l T P d); auto with coc core arith sets.

apply trans_conv_exp with (Pair_l T P d); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_lred with (Pair_l P b d); auto with coc core arith sets.

apply trans_conv_exp with (Pair_l P b d); auto with coc core arith sets.
Qed.


  Lemma conv_conv_llift :
   forall (a b : lterm) n k,
   conv a b -> conv (llift_rec n a k) (llift_rec n b k).
intros.
elim H; intros; auto with coc core arith sets.
apply trans_conv_lred with (llift_rec n P k); auto with coc core arith sets.

apply trans_conv_exp with (llift_rec n P k); auto with coc core arith sets.
Qed.
 

  Lemma conv_conv_lsubst :
   forall (a b c d : lterm) k,
   conv a b -> conv c d -> conv (lsubst_rec a c k) (lsubst_rec b d k).
intros.
apply trans_conv_conv with (lsubst_rec a d k).
elim H0; intros; auto with coc core arith sets.
apply trans_conv_lred with (lsubst_rec a P k); auto with coc core arith sets.

apply trans_conv_exp with (lsubst_rec a P k); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_conv with (lsubst_rec P d k); auto with coc core arith sets.

apply trans_conv_conv with (lsubst_rec P d k); auto with coc core arith sets.
apply sym_conv; auto with coc core arith sets.
Qed.

  Hint Resolve conv_conv_prod conv_conv_llift conv_conv_lsubst: coc.


  Lemma refl_par_lred1 : forall M, par_lred1 M M.
simple induction M; auto with coc core arith sets.
Qed.

  Hint Resolve refl_par_lred1: coc.


  Lemma lred1_par_lred1 : forall M N, lred1 M N -> par_lred1 M N.
simple induction 1; auto with coc core arith sets; intros.

Qed.

  Hint Resolve lred1_par_lred1: coc.


  Lemma lred_par_lred : forall M N, lred M N -> par_lred M N.
red in |- *; simple induction 1; intros; auto with coc core arith sets.
apply t_trans with P; auto with coc core arith sets.
Qed.


  Lemma par_lred_lred : forall M N, par_lred M N -> lred M N.
simple induction 1.
simple induction 1; intros; auto with coc core arith sets.
apply trans_lred with (App_l Typ (Abs_l T M') N'); auto with coc core arith sets.
apply trans_lred with (Pi1_l (Pair_l T M' N0)); auto with coc core arith sets.
apply trans_lred with (Pi2_l (Pair_l T M0 N')); auto with coc core arith sets.

intros.
apply trans_lred_lred with y; auto with coc core arith sets.
Qed.

  Hint Resolve lred_par_lred par_lred_lred: coc.


  Lemma par_lred1_llift :
   forall n (a b : lterm),
   par_lred1 a b -> forall k, par_lred1 (llift_rec n a k) (llift_rec n b k).
simple induction 1; simpl in |- *; auto with coc core arith sets.
intros.
rewrite distr_llift_lsubst; auto with coc core arith sets.
Qed.


  Lemma par_lred1_lsubst :
   forall c d : lterm,
   par_lred1 c d ->
   forall a b : lterm,
   par_lred1 a b -> forall k, par_lred1 (lsubst_rec a c k) (lsubst_rec b d k).
simple induction 1; simpl in |- *; auto with coc core arith sets; intros.
rewrite distr_lsubst; auto with coc core arith sets.

elim (lt_eq_lt_dec k n); auto with coc core arith sets; intro a0.
elim a0; intros; auto with coc core arith sets.
unfold llift in |- *.
apply par_lred1_llift; auto with coc core arith sets.
Qed.


  Lemma inv_par_lred_abs :
   forall (P : Prop) T (U x : lterm),
   par_lred1 (Abs_l T U) x ->
   (forall T' (U' : lterm), x = Abs_l T' U' -> par_lred1 U U' -> P) -> P.
do 5 intro.
inversion_clear H; intros.
apply H with T' M'; auto with coc core arith sets.
Qed.

  Lemma inv_par_lred_pair :
   forall (P : Prop) T (U V x : lterm),
   par_lred1 (Pair_l T U V) x ->
   (forall T' (U' V' : lterm), x = Pair_l T' U' V' -> par_lred1 U U' -> par_lred1 V V' -> P) -> P.
do 6 intro.
inversion_clear H; intros.
apply H with T' M' N'; auto with coc core arith sets.
Qed.

  Hint Resolve par_lred1_llift par_lred1_lsubst: coc.



  Lemma sublterm_abs : forall t (m : lterm), sublterm m (Abs_l t m).
intros.
apply Sbtrm_bind with t; auto with coc core arith sets.
Qed.

  Lemma sublterm_prod : forall t (m : lterm), sublterm m (Prod_l t m).
intros.
apply Sbtrm_bind with t; auto with coc core arith sets.
Qed.

  Lemma sublterm_sum : forall t (m : lterm), sublterm m (Sum_l t m).
intros.
apply Sbtrm_bind with t; auto with coc core arith sets.
Qed.

  Lemma sublterm_subset : forall t (m : lterm), sublterm m (Subset_l t m).
intros.
apply Sbtrm_bind with t; auto with coc core arith sets.
Qed.

  Lemma sublterm_let_in : forall t (m : lterm), sublterm m (Let_in_l t m).
intros.
apply Sbtrm_bind with t; auto with coc core arith sets.
Qed.

Hint Resolve sublterm_abs sublterm_prod sublterm_sum sublterm_subset
  sublterm_let_in : coc.


(*
  Lemma mem_sort_ref: (s:sort)(n:nat)~(mem_sort s (Ref_l n)).
(Red; Intros).
Cut (b:lterm)(mem_sort s b)->b=(Ref_l n)->False.
Intros.
(App_lly H0 with (Ref_l n); Auto with coc core arith sets).

Do 2 Intro.
(Elim H0 using clos_refl_trans_ind_left; Intros; Auto with coc core arith sets).
Discriminate H1.

Rewrite H4 in H3.
(Inversion_clear H3; Inversion_clear H5).
Save.
*)

  Lemma mem_sort_llift :
   forall t n k s, mem_sort s (llift_rec n t k) -> mem_sort s t.
simple induction t; simpl in |- *; intros; auto with coc core arith sets.
generalize H; elim (le_gt_dec k n); intros; auto with coc core arith sets.
inversion_clear H0.

inversion_clear H1.
apply mem_abs_l; apply H with n k; auto with coc core arith sets.

apply mem_abs_r; apply H0 with n (S k); auto with coc core arith sets.

inversion_clear H2.
apply mem_app_T; apply H with n k; auto with coc core arith sets.
apply mem_app_l; apply H0 with n k; auto with coc core arith sets.
apply mem_app_r; apply H1 with n k; auto with coc core arith sets.

inversion_clear H2.
apply mem_pair_T ; apply H with n k; auto with coc core arith sets.
apply mem_pair_l ; apply H0 with n k; auto with coc core arith sets.
apply mem_pair_r ; apply H1 with n k; auto with coc core arith sets.

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


  Lemma mem_sort_lsubst :
   forall (b a : lterm) n s,
   mem_sort s (lsubst_rec a b n) -> mem_sort s a \/ mem_sort s b.
simple induction b; simpl in |- *; intros; auto with coc core arith sets.

generalize H; elim (lt_eq_lt_dec n0 n); [ intro a0 | intro b0 ].
elim a0; intros.
inversion_clear H0.

left.
apply mem_sort_llift with n0 0; auto with coc core arith sets.

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

inversion_clear H2 ; [
elim H with a n s; auto with coc core arith sets |
elim H0 with a n s; auto with coc core arith sets |
elim H1 with a n s; intros; auto with coc core arith sets].

inversion_clear H2 ; [
elim H with a n s; auto with coc core arith sets |
elim H0 with a n s; auto with coc core arith sets |
elim H1 with a n s; intros; auto with coc core arith sets].

inversion_clear H1 ; [
elim H with a n s; auto with coc core arith sets |
elim H0 with a (S n) s; intros; auto with coc core arith sets].
inversion_clear H1.
elim (H _ _ _ H2) ; intros ; auto with coc core arith sets.
elim (H0 _ _ _ H2) ; intros ; auto with coc core arith sets.

inversion_clear H1 ; [
elim H with a n s; auto with coc core arith sets |
elim H0 with a (S n) s; auto with coc core arith sets ].

inversion_clear H0 ; [
elim H with a n s; auto with coc core arith sets ].
inversion_clear H0 ; [
elim H with a n s; auto with coc core arith sets ].

inversion_clear H1 ; [
elim H with a n s; auto with coc core arith sets |
elim H0 with a (S n) s; intros; auto with coc core arith sets].
Qed.

  Lemma lred_sort_mem : forall t s, lred t (Srt_l s) -> mem_sort s t.
intros.
pattern t in |- *.
apply lred1_lred_ind with (Srt_l s); auto with coc core arith sets.
do 4 intro.
elim H0; intros ; try (inversion_clear H4; auto with coc core arith sets).
elim mem_sort_lsubst with M0 N 0 s; intros; auto with coc core arith sets.
apply mem_pi1 ; auto with coc core arith sets.
apply mem_pi2 ; auto with coc core arith sets.
Qed.

  Lemma lred_normal : forall u v, lred u v -> normal u -> u = v.
simple induction 1; auto with coc core arith sets; intros.
absurd (lred1 u N); auto with coc core arith sets.
absurd (lred1 P N); auto with coc core arith sets.
elim (H1 H3).
unfold not in |- *; intro; apply (H3 N); auto with coc core arith sets.
Qed.



  Lemma sn_lred_sn : forall a b : lterm, sn a -> lred a b -> sn b.
unfold sn in |- *.
simple induction 2; intros; auto with coc core arith sets.
apply Acc_inv with P; auto with coc core arith sets.
Qed.


  Lemma commut_lred1_sublterm : commut _ sublterm (transp _ lred1).
red in |- *.
simple induction 1; intros.
inversion_clear H0.
exists (Abs_l t z); auto with coc core arith sets.

exists (Prod_l t z); auto with coc core arith sets.

exists (Sum_l t z); auto with coc core arith sets.

exists (Subset_l t z); auto with coc core arith sets.

exists (Let_in_l t z); auto with coc core arith sets.

inversion_clear H0.
exists (Abs_l z n); auto with coc core arith sets.

exists (App_l z u v); auto with coc core arith sets.

exists (App_l T z v); auto with coc core arith sets.

exists (App_l T u z); auto with coc core arith sets.

exists (Pair_l z u v); auto with coc core arith sets.
exists (Pair_l T z v); auto with coc core arith sets.
exists (Pair_l T u z); auto with coc core arith sets.

exists (Prod_l z n); auto with coc core arith sets.
exists (Sum_l z n); auto with coc core arith sets.
exists (Subset_l z n); auto with coc core arith sets.
exists (Pi1_l z); auto with coc core arith sets.
exists (Pi2_l z); auto with coc core arith sets.
exists (Let_in_l z n); auto with coc core arith sets.
Qed.


 Lemma sublterm_sn :
   forall a : lterm, sn a -> forall b : lterm, sublterm b a -> sn b.
unfold sn in |- *.
simple induction 1; intros.
apply Acc_intro; intros.
elim commut_lred1_sublterm with x b y; intros; auto with coc core arith sets.
apply H1 with x0; auto with coc core arith sets.
Qed.


  Lemma sn_prod : forall A, sn A -> forall B, sn B -> sn (Prod_l A B).
unfold sn in |- *.
simple induction 1.
simple induction 3; intros.
apply Acc_intro; intros.
inversion_clear H5; auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply Acc_intro; auto with coc core arith sets.
Qed.

  Lemma sn_sum : forall A, sn A -> forall B, sn B -> sn (Sum_l A B).
unfold sn in |- *.
simple induction 1.
simple induction 3; intros.
apply Acc_intro; intros.
inversion_clear H5; auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply Acc_intro; auto with coc core arith sets.
Qed.

  Lemma sn_pair : forall T, sn T -> forall A, sn A -> forall B, sn B -> sn (Pair_l T A B).
unfold sn.
simple induction 1.
simple induction 3.
simple induction 3 ; intros.
apply Acc_intro; intros.
inversion_clear H8; auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply Acc_intro; auto with coc core arith sets.
apply Acc_intro; auto with coc core arith sets.

apply H4 ; auto with coc core arith sets.
apply Acc_intro; auto with coc core arith sets.
Qed.

  Lemma sn_subset : forall A, sn A -> forall B, sn B -> sn (Subset_l A B).
unfold sn in |- *.
simple induction 1.
simple induction 3; intros.
apply Acc_intro; intros.
inversion_clear H5; auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply Acc_intro; auto with coc core arith sets.
Qed.

  Lemma sn_let_in : forall A, sn A -> forall B, sn B -> sn (Let_in_l A B).
unfold sn in |- *.
simple induction 1.
simple induction 3; intros.
apply Acc_intro; intros.
inversion_clear H5; auto with coc core arith sets.
apply H1; auto with coc core arith sets.
apply Acc_intro; auto with coc core arith sets.
Qed.


  Lemma sn_lsubst : forall T M, sn (lsubst T M) -> sn M.
intros.
cut (forall t, sn t -> forall m : lterm, t = lsubst T m -> sn m).
intros.
apply H0 with (lsubst T M); auto with coc core arith sets.

unfold sn in |- *.
simple induction 1; intros.
apply Acc_intro; intros.
apply H2 with (lsubst T y); auto with coc core arith sets.
rewrite H3.
unfold lsubst in |- *; auto with coc core arith sets.
Qed.
