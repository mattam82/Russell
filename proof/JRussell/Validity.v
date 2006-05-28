Require Import Lambda.Terms.
Require Import Lambda.Reduction.
Require Import Lambda.Conv.
Require Import Lambda.Conv_Dec.
Require Import Lambda.LiftSubst.
Require Import Lambda.Env.
Require Import Lambda.JRussell.Types.
Require Import Lambda.JRussell.Basic.
Require Import Lambda.JRussell.Conversion.
Require Import Lambda.JRussell.Coercion.
Require Import Lambda.JRussell.Thinning.
Require Import Lambda.JRussell.Substitution.
Require Import Lambda.JRussell.PreFunctionality.
Require Import Lambda.JRussell.Generation.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Lemma app_cons_app_app : forall e' a e, e' ++ a :: e = (e' ++ a :: nil) ++ e.
Proof.
  induction e' ; simpl ; intros ; auto.
  rewrite IHe'.
  reflexivity.
Qed.

Lemma strength_sort_judgement : forall e s s', e |-= Srt s : Srt s' -> nil |-= Srt s : Srt s'.
Proof.
  intros.
  destruct s.
  elim left_not_kind with e (Srt kind) (Srt s') ; auto.

  pose (generation_sort H).
  pose (equiv_kind e0).
  rewrite e1.
  auto with coc.

  pose (generation_sort H).
  pose (equiv_kind e0).
  rewrite e1.
  auto with coc.
Qed.

Lemma trunc_list : forall e, trunc _ (length e) e nil.
Proof.
  induction e ; simpl ;
  constructor ; auto.
Qed.

Lemma sort_judgement_empty_env : forall s s', nil |-= Srt s : Srt s' ->
  forall e, consistent e -> e |-= Srt s : Srt s'.
Proof.
  intros.
  pose (thinning_n (trunc_list e) H0 H). 
  unfold lift in t ; simpl in t.
  assumption.
Qed.

Lemma weak_one_sort_judgement : forall T e s s', T :: e |-= Srt s : Srt s' -> 
  e |-= Srt s : Srt s'.
Proof.
  intros.
  pose (typ_consistent H).
  pose (strength_sort_judgement H).
  inversion c.
  apply (sort_judgement_empty_env t H2).
Qed.

Hint Resolve weak_one_sort_judgement : coc.

Lemma validity_ind : 
  (forall e t T, e |-= t : T ->
  T = Srt kind \/ exists s, e |-= T : Srt s) /\
  (forall e T U s, e |-= T >> U : s ->
  e |-= T : Srt s /\ e |-= U : Srt s) /\
  (forall e t u T, e |-= t = u : T ->
  (e |-= t : T /\ e |-= u : T) /\
  (T = Srt kind \/ exists s, e |-= T : Srt s)).
Proof.
  apply typ_coerce_jeq_ind with 
  (P := fun e t T => fun H : e |-= t : T =>
  T = Srt kind \/ exists s, e |-= T : Srt s)
  (P0 := fun e T U s => fun H : e |-= T >> U : s =>
  e |-= T : Srt s /\ e |-= U : Srt s)
  (P1 := fun e t u T => fun H : e |-= t = u : T =>
  (e |-= t : T /\ e |-= u : T) /\
  (T = Srt kind \/ exists s, e |-= T : Srt s)) ;
  simpl ; intros ; auto with coc ; try discriminate ; 
  try (destruct H ; discriminate) ;  try (destruct H1 ; discriminate).

  destruct H.
  right.
  inversion H.
  rewrite H1 in t.
  exists kind.
  change (Srt kind) with (lift 1 (Srt kind)).
  apply type_weak with kind ; auto with coc.
  
  destruct H.
  pose (generation_sort H).
  right.
  exists s.
  change (Srt s) with (lift 1 (Srt s)).
  apply type_weak with s ; auto with coc.

  destruct H.
  left ; rewrite H ; auto with coc.

  destruct H.
  right.
  exists x.
  change (Srt x) with (lift 1 (Srt x)).
  apply type_weak with s ; auto with coc.

  right.
  exists s2 ; apply type_prod with s1 ; auto with coc.

  destruct H0 ; try discriminate.
  destruct H0.
  right.
  pose (generation_prod H0).
  destruct e0.
  destruct H1.
  destruct H1.
  destruct H2.

  exists x1.
  change (Srt x1) with (subst v (Srt x1)).
  apply substitution with V ; auto with coc.

  right.
  exists s3 ; apply type_sum with s1 s2 ; auto with coc.

  destruct H0.
  left ; auto.
  destruct H0.
  right.
  exists x.
  inversion H0.
  rewrite H3 ; rewrite H4.
  apply weak_one_sort_judgement with T ; assumption.
  apply weak_one_sort_judgement with T; assumption.
  
  right.
  pose (typ_consistent t).
  exists kind.
  apply sort_judgement_empty_env ; auto.
  destruct s;
  destruct H1 ; destruct H2 ; rewrite H3 ; auto with coc.

  destruct H ; try discriminate.
  destruct H.
  pose (generation_sum H).
  destruct e0.
  do 2 destruct H0.
  intuition.
  right ; exists x0 ; assumption.

  destruct H ; try discriminate.
  destruct H.
  pose (generation_sum H).
  destruct e0.
  do 2 destruct H0.
  intuition.
  right ; exists x1 ; auto with coc.
  change (Srt x1) with (subst (Pi1 t) (Srt x1)).
  apply substitution with U ; auto with coc.
  apply type_pi1 with V ; auto with coc.

  destruct H.
  destruct H0 ; try contradiction.
  destruct H.
  right ; exists s ; auto.

  right ; intuition.

  exists s ; intuition.

  destruct H ; intuition.

  destruct H.
  change (Srt s) with (lift 1 (Srt s)).
  split ; apply type_weak with s' ; auto.

  split ; apply type_prod with s ; auto with coc.

  split ; apply type_sum with s s' ; auto with coc.

  split ; auto with coc ; apply type_subset ; auto with coc.

  split ; auto with coc ; apply type_subset ; auto with coc.

  intuition.

  intuition.

  (* Judgemental equality *)
  destruct H.
  destruct H.
  split.
  split ; apply type_weak with s ; auto with coc.

  destruct H1.
  rewrite H1 ; left ; auto.
  destruct H1.
  right ; exists x ; change (Srt x) with (lift 1 (Srt x)) ; 
  apply type_weak with s ; auto with coc.

  (* Prod *)
  do 2 destruct H.
  do 2 destruct H0.
  split.
  split ; apply type_prod with s1 ; auto with coc.
  apply (type_conv_env H4).
  apply conv_env_hd with s1 ; auto with coc.

  destruct H3.
  left ; auto.
  right.
  destruct H3.
  exists x.
  apply weak_one_sort_judgement with U ; auto.

  (* Abs *)  
  do 2 destruct H.
  do 2 destruct H1.
  split.
  split ; try apply type_abs with s1 s2 ; auto with coc.
  assert(conv_in_env (A :: e) (A' :: e)).
  apply conv_env_hd with s1 ; auto with coc.
  pose (type_conv_env H5 H6).
  apply type_conv with (Prod A' B) s2 ; auto with coc.
  apply type_abs with s1 s2 ; auto with coc.
  apply (type_conv_env t H6).
  apply coerce_prod with s1 ; auto with coc.
  apply (type_conv_env t H6).
  
  right.
  exists s2 ; apply type_prod with s1 ; auto with coc.
  
  (* App *)
  do 2 destruct H.
  do 2 destruct H0.
  destruct H1 ; try discriminate.
  destruct H1.
  pose (generation_prod H1).
  destruct e0.
  do 2 destruct H5.
  destruct H6.
  split.
  split ; try apply type_app with A ; auto with coc.
  apply type_conv with (subst N' B) x1 ; auto with coc.
  apply type_app with A ; auto with coc.
  apply coerce_conv ; auto with coc.
  change (Srt x1) with (subst N (Srt x1)).
  apply jeq_sym.
  apply pre_functionality with A ; auto with coc.

  right ; exists x1.
  change (Srt x1) with (subst N (Srt x1)).
  apply substitution with A ; auto with coc.

  (* Beta *)
  split.
  split ; try apply type_app with A ; auto with coc.
  apply type_abs with s1 s2 ; auto with coc.
  apply substitution with A ; auto.

  right.
  exists s2.
  change (Srt s2) with (subst N (Srt s2)).
  apply substitution with A ; auto with coc.
(*
  (* Red *)
  do 2 destruct H0.
  do 2 destruct H.
  split.
  split ; apply type_conv with A s ; auto with coc.

  right.
  exists s ; auto.

  (* Exp *)
  do 2 destruct H0.
  do 2 destruct H.
  split.
  split ; apply type_conv with B s ; auto with coc.

  right.
  exists s ; auto.
*)
  (* Sum *)
  do 2 destruct H.
  do 2 destruct H0.
  split.
  split ; apply type_sum with s1 s2 ; auto with coc.
  apply (type_conv_env H4).
  apply conv_env_hd with s1 ; auto with coc.

  right ; exists kind.
  pose (typ_consistent H).
  apply sort_judgement_empty_env ; auto with coc.
  
  inversion s ;
  destruct H5 ;
  destruct H6 ;
  try rewrite H7 ; auto with coc.

  (* Pair *)  
  do 2 destruct H.
  do 2 destruct H0.
  do 2 destruct H1.
  do 2 destruct H2.
  split.
  split ; try apply type_pair with s1 s2 s3 ; auto with coc.
  apply type_conv with (Sum A' B') s3; auto with coc.
  apply type_pair with s1 s2 s3 ; auto with coc.
  apply type_conv with A s1 ; auto with coc.
  assert(conv_in_env (A :: e) (A' :: e)).
  apply conv_env_hd with s1 ; auto with coc.
  apply (type_conv_env H6 H11).
  
  apply type_conv with (subst u B) s2 ; auto with coc.
  apply coerce_conv ; auto with coc.
  apply jeq_trans with (subst u' B) ; auto with coc.
  change (Srt s2) with (subst u (Srt s2)).
  apply pre_functionality with A ; auto with coc.
  change (Srt s2) with (subst u' (Srt s2)).
  apply substitution_jeq with A ; auto with coc.

  apply coerce_conv ; auto with coc.
  apply jeq_sum with s1 s2 ; auto with coc.
  apply jeq_sym.
  apply jeq_conv_env with (A :: e) ; auto with coc.
  apply conv_env_hd with s1 ; auto with coc.

  right.
  exists s3 ; apply type_sum with s1 s2 ; auto with coc.

  (* Pi1 *)
  do 2 destruct H.
  split ; try (split ; apply type_pi1 with B ; auto with coc).
  right.
  destruct H0 ; try discriminate.
  destruct H0.
  pose (generation_sum H0).
  destruct e0.
  do 3 destruct H2.
  exists x0 ; auto.

  (* Pi1 red *)
  split.
  split ; auto.
  apply type_pi1 with B ; auto with coc.
  apply type_pair with s1 s2 s3 ; auto with coc.
  right ; exists s1 ; assumption.

  (* Pi2 *)
  do 2 destruct H.
  destruct H0 ; try discriminate.
  destruct H0.
  pose (generation_sum H0).
  destruct e0.
  do 3 destruct H2.
  split.
  split. 
  apply type_pi2 with A ; auto with coc.
  apply type_conv with (subst (Pi1 t') B) x1.
  apply type_pi2 with A ; auto with coc.
  intuition.
  apply coerce_conv ; auto.
  change (Srt x1) with (subst (Pi1 t) (Srt x1)).
  apply jeq_sym.
  apply pre_functionality with A ; auto with coc.
  apply type_pi1 with B ; auto with coc.
  apply jeq_pi1 with B ; auto with coc.

  right.
  exists x1 ; intuition ; auto.
  change (Srt x1) with (subst (Pi1 t) (Srt x1)).
  apply substitution with A ; auto with coc.
  apply type_pi1 with B ; auto with coc.

  (* Pi2 red *)
  split.
  split ; auto.
  apply type_conv with (subst (Pi1 (Pair (Sum A B) u v)) B) s2 ; auto with coc.
  apply type_pi2 with A ; auto with coc.
  apply type_pair with s1 s2 s3 ; auto with coc.
  apply coerce_conv ; auto.
  change (Srt s2) with (subst (Pi1 (Pair (Sum A B) u v)) (Srt s2)).
  apply pre_functionality with A ; auto with coc.
  apply type_pi1 with B ; auto with coc.
  apply type_pair with s1 s2 s3 ; auto with coc.
  
  apply jeq_pi1_red with s1 s2 s3 ; auto with coc.

  right.
  exists s2.
  change (Srt s2) with (subst u (Srt s2)).
  apply substitution with A ; auto with coc.

  (* Subset *)
  do 2 destruct H.
  do 2 destruct H0.
  split.
  split ; try apply type_subset ; auto with coc.
  
  apply type_conv_env with (A :: e) ; auto with coc.
  apply conv_env_hd with set ; auto.
  right.
  exists kind.
  apply sort_judgement_empty_env ; auto with coc.
  apply (typ_consistent H).

  (* Sym *)
  do 2 destruct H.
  split ; try (split ; auto) ; auto.

  (* Trans *)
  do 2 destruct H.
  do 2 destruct H0.
  split ; auto.

  (* Coerce *)
  do 2 destruct H.
  destruct H0.
  split ; auto.
  split ; apply type_conv with A s ; auto.
  right.
  exists s ; assumption.
Qed.

Lemma validity_typ :
  forall e t T, e |-= t : T ->
  T = Srt kind \/ exists s, e |-= T : Srt s.
Proof (proj1 validity_ind).

Lemma validity_coerce :
  forall e T U s, e |-= T >> U : s ->
  e |-= T : Srt s /\ e |-= U : Srt s.
Proof (proj1 (proj2 validity_ind)).

Lemma validity_jeq :
 forall e t u T, e |-= t = u : T ->
 (e |-= t : T /\ e |-= u : T) /\
 (T = Srt kind \/ exists s, e |-= T : Srt s).
Proof (proj2 (proj2 validity_ind)).

Inductive conv_env : env -> env -> Prop :=
  | conv_env_hd : forall e t u s, e |-= t = u : Srt s -> conv_env (t :: e) (u :: e)
  | conv_env_tl :
      forall e f t, conv_in_env e f -> conv_env (t :: e) (t :: f).

Lemma conv_env_conv_in_env : forall e e', conv_env e e' -> conv_in_env e e'.
Proof.
  induction 1.
  pose (validity_jeq H).
  destruct a.
  destruct H0.
  apply (Conversion.conv_env_hd) with s ; auto.
  constructor ; auto.
Qed.

Lemma type_conv_env : forall e t T, e |-= t : T -> 
  forall f, conv_env e f -> f |-= t : T.
Proof.
  intros.
  apply Conversion.type_conv_env with e ; auto.
  apply conv_env_conv_in_env ; auto.
Qed.

Lemma coerce_conv_env : forall e T U s, e |-= T >> U : s -> 
  forall f, conv_env e f -> f |-= T >> U : s.
Proof.
  intros.
  apply Conversion.coerce_conv_env with e ; auto.
  apply conv_env_conv_in_env ; auto.
Qed.

Lemma jeq_conv_env : forall e U V T, e |-= U = V : T ->
  forall f, conv_env e f -> f |-= U = V : T.
Proof.
  intros.
  apply Conversion.jeq_conv_env with e ; auto.
  apply conv_env_conv_in_env ; auto.
Qed.

Lemma functionality_rec : forall g (d : term) t, 
  forall d', g |-= d = d' : t ->
  forall e U T, e |-= U : T ->
  forall f n, sub_in_env d t n e f -> trunc _ n f g -> 
  f |-= (subst_rec d U n) = (subst_rec d' U n) : (subst_rec d T n).
Proof.
  intros.
  apply pre_functionality_rec with g t e; auto.
  pose (validity_jeq H).
  destruct a.
  destruct H3.
  assumption.
Qed.

Lemma functionality :forall e (d : term) t, e |-= d : t -> 
  forall d', e |-= d = d' : t ->
  forall U T, t :: e |-= U : T ->
  e |-= (subst d U) = (subst d' U) : (subst d T).
Proof.
  intros.
  unfold subst ; pose functionality_rec.
  apply (@pre_functionality_rec e d t H d' H0 (t :: e) U T H1).
  constructor.
  constructor.
Qed.

Lemma jeq_type_l : forall e u v T, e |-= u = v : T -> e |-= u : T.
Proof.
  intros.
  pose (validity_jeq H).
  intuition.
Qed.

Lemma jeq_type_r : forall e u v T, e |-= u = v : T -> e |-= v : T.
Proof.
  intros.
  pose (validity_jeq H).
  intuition.
Qed.

Lemma coerce_sort_l : forall e U V s, e |-= U >> V : s -> e |-= U : Srt s.
Proof.
  intros.
  pose (validity_coerce H).
  intuition.
Qed.

Lemma coerce_sort_r : forall e U V s, e |-= U >> V : s -> e |-= V : Srt s.
Proof.
  intros.
  pose (validity_coerce H).
  intuition.
Qed.

Hint Resolve jeq_type_l jeq_type_r coerce_sort_l coerce_sort_r : coc.

Lemma jeq_subst_par : forall e u u' v v' A B, e |-= u = u' : A -> A :: e |-= v = v' : B ->
  e |-= subst u v = subst u' v' : subst u B.
Proof.
  intros.
  pose (jeq_type_l H).
  pose (jeq_type_l H0).

  apply jeq_trans with (subst u v') ; auto with coc.
  apply substitution_jeq with A ; auto with coc.
  apply functionality with A ; auto with coc.
  apply (jeq_type_r H0).
Qed.


