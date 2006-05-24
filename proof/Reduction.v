Require Import Lambda.Terms.
Require Import Lambda.LiftSubst.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Inductive red1 : term -> term -> Prop :=
| beta : forall M N T, red1 (App (Abs T M) N) (subst N M)
| pi1 : forall T M N, red1 (Pi1 (Pair T M N)) M
| pi2 : forall T M N, red1 (Pi2 (Pair T M N)) N
| abs_red_l : forall M M', red1 M M' -> forall N, red1 (Abs M N) (Abs M' N)
| abs_red_r : forall M M', red1 M M' -> forall N, red1 (Abs N M) (Abs N M')
| app_red_l : forall M1 N1, red1 M1 N1 -> forall M2, red1 (App M1 M2) (App N1 M2)
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
        forall M N, red1 M N -> red1 (Pi2 M) (Pi2 N).
      
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
    | par_pi1 : forall M M', par_red1 M M' -> 
      forall T N, par_red1 (Pi1 (Pair T M N)) M'
    | par_pi2 : forall N N', par_red1 N N' -> forall T M,
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
        forall M M', par_red1 M M' -> par_red1 (Pi2 M) (Pi2 M').

  Definition par_red := clos_trans term par_red1.

  Hint Resolve beta pi1 pi2 abs_red_l abs_red_r app_red_l app_red_r pair_red_T pair_red_l pair_red_r : coc.
  Hint Resolve prod_red_l prod_red_r sum_red_l sum_red_r subset_red_l subset_red_r pi1_red pi2_red  : coc.
  Hint Resolve refl_red refl_conv: coc.
  Hint Resolve par_beta par_pi1 par_pi2 sort_par_red ref_par_red abs_par_red app_par_red pair_par_red
    prod_par_red sum_par_red subset_par_red pi1_par_red pi2_par_red: coc.

  Hint Unfold par_red: coc.


Section Normalisation_Forte.

  Definition normal t : Prop := forall u, ~ red1 t u.

  Definition sn : term -> Prop := Acc (transp _ red1).

End Normalisation_Forte.

  Hint Unfold sn: coc.



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

  Hint Resolve red_red_app red_red_abs red_red_prod: coc.
  Hint Resolve red_red_pair red_red_sum red_red_subset red_red_pi1 red_red_pi2 : coc.


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

  Lemma red_ref_ref : forall n t, red (Ref n) t -> t <> Ref n -> False.
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

Lemma conv_conv_abs : forall a b c d : term, conv a b -> conv c d -> conv (Abs a c) (Abs b d).
Proof.
intros.
apply trans_conv_conv with (Abs a d).
elim H0; intros; auto with coc core arith sets.
apply trans_conv_red with (Abs a P); auto with coc core arith sets.

apply trans_conv_exp with (Abs a P); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_red with (Abs P d); auto with coc core arith sets.

apply trans_conv_exp with (Abs P d); auto with coc core arith sets.
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
apply trans_conv_conv with (Pair T a d).
elim H1; intros; auto with coc core arith sets.
apply trans_conv_red with (Pair T a P); auto with coc core arith sets.

apply trans_conv_exp with (Pair T a P); auto with coc core arith sets.

apply trans_conv_conv with (Pair T b d); auto with coc core arith sets.
elim H0; intros; auto with coc core arith sets.
apply trans_conv_red with (Pair T P d); auto with coc core arith sets.

apply trans_conv_exp with (Pair T P d); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_red with (Pair P b d); auto with coc core arith sets.

apply trans_conv_exp with (Pair P b d); auto with coc core arith sets.
Qed.


Lemma conv_conv_app : forall a b c d : term, conv a b -> conv c d -> conv (App a c) (App b d).
Proof.
intros.
apply trans_conv_conv with (App a d).
elim H0; intros; auto with coc core arith sets.
apply trans_conv_red with (App a P); auto with coc core arith sets.

apply trans_conv_exp with (App a P); auto with coc core arith sets.

elim H; intros; auto with coc core arith sets.
apply trans_conv_red with (App P d); auto with coc core arith sets.

apply trans_conv_exp with (App P d); auto with coc core arith sets.
Qed.

Lemma conv_conv_pi1 : forall a b : term, conv a b -> conv (Pi1 a) (Pi1 b).
Proof.
intros.
elim H; intros; auto with coc core arith sets.
apply trans_conv_red with (Pi1 P); auto with coc core arith sets.

apply trans_conv_exp with (Pi1 P); auto with coc core arith sets.
Qed.

Lemma conv_conv_pi2 : forall a b : term, conv a b -> conv (Pi2 a) (Pi2 b).
Proof.
intros.
elim H; intros; auto with coc core arith sets.
apply trans_conv_red with (Pi2 P); auto with coc core arith sets.

apply trans_conv_exp with (Pi2 P); auto with coc core arith sets.
Qed.

Hint Resolve conv_conv_pi1 conv_conv_pi2 : coc.

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
apply trans_red with (Pi1 (Pair T M' N0)); auto with coc core arith sets.
apply trans_red with (Pi2 (Pair T M0 N')); auto with coc core arith sets.

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

  Lemma inv_par_red_pair :
   forall (P : Prop) T (U V x : term),
   par_red1 (Pair T U V) x ->
   (forall T' (U' V' : term), x = Pair T' U' V' -> par_red1 U U' -> par_red1 V V' -> P) -> P.
do 6 intro.
inversion_clear H; intros.
apply H with T' M' N'; auto with coc core arith sets.
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

Hint Resolve subterm_abs subterm_prod subterm_sum subterm_subset
 : coc.


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

inversion_clear H2 ; [
elim H with a n s; auto with coc core arith sets |
elim H0 with a n s; auto with coc core arith sets |
elim H1 with a n s; intros; auto with coc core arith sets].

inversion_clear H1 ; [
elim H with a n s; auto with coc core arith sets |
elim H0 with a (S n) s; intros; auto with coc core arith sets].
inversion_clear H1 ; [
elim H with a n s; auto with coc core arith sets |
elim H0 with a (S n) s; intros; auto with coc core arith sets].
inversion_clear H1.
elim (H _ _ _ H2) ; intros ; auto with coc core arith sets.
elim (H0 _ _ _ H2) ; intros ; auto with coc core arith sets.
inversion_clear H0 ; [
elim H with a n s; auto with coc core arith sets ].
inversion_clear H0 ; [
elim H with a n s; auto with coc core arith sets ].
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

inversion_clear H0.
exists (Abs z n); auto with coc core arith sets.

exists (App z v); auto with coc core arith sets.

exists (App u z); auto with coc core arith sets.

exists (Pair z u v); auto with coc core arith sets.
exists (Pair T z v); auto with coc core arith sets.
exists (Pair T u z); auto with coc core arith sets.

exists (Prod z n); auto with coc core arith sets.
exists (Sum z n); auto with coc core arith sets.
exists (Subset z n); auto with coc core arith sets.
exists (Pi1 z); auto with coc core arith sets.
exists (Pi2 z); auto with coc core arith sets.
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

  Lemma sn_pair : forall T, sn T -> forall A, sn A -> forall B, sn B -> sn (Pair T A B).
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

  Lemma sn_subset : forall A, sn A -> forall B, sn B -> sn (Subset A B).
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
