Require Import JRussell.Types.
Require Import JRussell.Validity.

Require Import Russell.Types.
Require Import Russell.Thinning.
Require Import Russell.Coercion.
Require Import Russell.Substitution.
Require Import Russell.Inversion.
Require Import Russell.Generation.
Require Import Russell.GenerationRange.
Require Import Russell.UnicityOfSorting.
Require Import Russell.Transitivity.

Require Import Lambda.Terms.
Require Import Lambda.Conv.
Require Import Lambda.LiftSubst.
Require Import Lambda.Reduction.
Require Import Lambda.Env.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Theorem jrussell_to_russell :
  (forall G t T, JRussell.Types.typ G t T -> G |- t : T) /\
  (forall G U V s, JRussell.Types.coerce G U V s -> G |- U : Srt s /\ G |- V : Srt s /\ 
  G |- U >> V : s) /\
  (forall G u v T, G |- u = v : T -> G |- u : T /\ G |- v : T /\ 
  conv u v).
Proof. 
  apply typ_coerce_jeq_ind with
  (P := fun G t T => fun H : JRussell.Types.typ G t T => G |- t : T)
  (P0 := fun G U V s => fun H : JRussell.Types.coerce G U V s => 
  G |- U : Srt s /\ G |- V : Srt s /\ 
  G |- U >> V : s)
  (P1 := fun G u v T => fun H : G |- u = v : T => G |- u : T /\ G |- v : T /\ 
  conv u v) ; simpl ; intros ; auto with coc.

  apply type_var ; auto with coc.
  apply wf_var with s ; auto.
  exists T ; auto.  
  constructor.

  apply thinning ; auto with coc.
  apply wf_var with s ; auto.

  apply type_abs with s1 s2 ; auto with coc.

  apply type_app with V ; auto with coc.

  apply type_pair with s1 s2 s3 ; auto with coc.
  
  apply type_prod with s1 ; auto with coc.

  apply type_sum with s1 s2 ; auto with coc.

  apply type_subset ; auto with coc.

  apply type_pi1 with V ; auto with coc.

  apply type_pi2 with U ; auto with coc.
  
  intuition.
  apply type_conv with U s ; auto with coc.

  intuition.

  intuition.
  change (Srt s) with (lift 1 (Srt s)).
  apply thinning ; auto with coc.
  apply wf_var with s' ; auto.
  change (Srt s) with (lift 1 (Srt s)).
  apply thinning ; auto with coc.
  apply wf_var with s' ; auto.
  apply thinning_coerce ; auto with coc.
  apply wf_var with s' ; auto.

  intuition ; try apply type_prod with s ; auto.
  apply coerce_prod with s ; auto.

  intuition ; try apply type_sum with s s' ; auto.
  apply coerce_sum with s s' ; auto.

  intuition ; try apply type_subset ; auto.

  intuition ; try apply type_subset ; auto.

  intuition.

  intuition.
  apply coerce_trans with B ; auto.

  assert(wf (B :: e)) by (apply wf_var with s) ; assumption.
  intuition ; try apply thinning ; auto.
  unfold lift ; apply conv_conv_lift ; assumption.

  intuition ; try (apply type_prod with s1 ; auto).
  apply typ_conv_env with (U :: e) ; auto.
  apply coerce_env_hd with s1 ; auto with coc.
  apply wf_var with s1 ; auto.

  intuition ; try apply type_abs with s1 s2 ; auto.
  assert(coerce_in_env (A :: e) (A' :: e)).
  apply coerce_env_hd with s1 ; auto with coc.
  assert(wf (A' :: e)) by apply wf_var with s1 ; assumption.
  apply type_conv with (Prod A' B) s2 ; auto with coc.
  apply type_abs with s1 s2 ; auto with coc.
  apply typ_conv_env with (A :: e) ; auto with coc.
  apply typ_conv_env with (A :: e) ; auto with coc.
  apply type_prod with s1 ; auto with coc.
  apply type_prod with s1 ; auto with coc.
  apply typ_conv_env with (A :: e) ; auto with coc.
  apply coerce_prod with s1 ; auto with coc.
  apply typ_conv_env with (A :: e) ; auto with coc.
  apply conv_conv_abs ; auto with coc.

  intuition ; try apply type_app with A ; auto with coc.
  destruct (type_sorted H0) ; intuition ; try discriminate.
  destruct H3.
  pose (generation_prod2 H3).
  intuition.
  destruct H6.
  assert(e |- subst N B : Srt x).
  change (Srt x) with (subst N (Srt x)).
  apply substitution with A ; auto with coc.
  assert(e |- subst N' B : Srt x).
  change (Srt x) with (subst N' (Srt x)).
  apply substitution with A ; auto with coc.
  apply type_conv with (subst N' B) x ; auto with coc.
  apply type_app with A ; auto with coc.
  apply coerce_conv with (subst N B) (subst N B) ; auto with coc.
  unfold subst ; apply conv_conv_subst ; auto with coc.
  apply conv_conv_app ; auto with coc.
  
  intuition ; try apply type_app with A ; auto with coc.
  apply type_abs with s1 s2 ; auto with coc.
  apply substitution with A ; auto.

  intuition.
  apply type_conv with A s ; auto with coc.
  apply type_conv with A s ; auto with coc.

  intuition ; auto with coc.
  apply type_conv with B s ; auto with coc.
  apply type_conv with B s ; auto with coc.

  intuition ; try apply type_sum with s1 s2 ; auto with coc.
  apply typ_conv_env with (A :: e) ; auto with coc.
  apply coerce_env_hd with s1 ; auto with coc.
  apply wf_var with s1 ; auto.
  apply conv_conv_sum ; auto with coc.

  assert(e |- subst u' B : Srt s2).
  change (Srt s2) with (subst u' (Srt s2)) ; auto with coc.
  apply substitution with A ; auto with coc ; intuition.
  assert(e |- subst u B : Srt s2).
  change (Srt s2) with (subst u (Srt s2)) ; auto with coc.
  apply substitution with A ; auto with coc ; intuition.
  assert(e |- subst u' B' : Srt s2).
  change (Srt s2) with (subst u' (Srt s2)) ; auto with coc.
  apply substitution with A ; auto with coc ; intuition.
  assert(coerce_in_env (A :: e) (A' :: e)).
  apply coerce_env_hd with s1 ; auto with coc ; intuition.
  assert(wf (A' :: e)).
  apply wf_var with s1 ; auto ; intuition.

  intuition ; try apply type_pair with s1 s2 s3 ; auto with coc.
  apply type_conv with (Sum A' B') s3 ; auto with coc.
  
  apply type_pair with s1 s2 s3 ; auto with coc.
  apply type_conv with A s1 ; auto with coc.
  apply typ_conv_env with (A :: e) ; auto with coc.
  apply type_conv with (subst u B) s2; auto with coc.
  apply conv_coerce ; auto.
  unfold subst ; apply conv_conv_subst ; auto.
  apply type_sum with s1 s2 ; auto with coc.
  apply type_sum with s1 s2 ; auto.
  apply typ_conv_env with (A :: e) ; auto with coc.
  apply conv_coerce ; auto.
  apply type_sum with s1 s2 ; auto.
  apply typ_conv_env with (A :: e) ; auto.
  apply type_sum with s1 s2 ; auto.
  apply conv_conv_sum ; auto with coc.
  apply conv_conv_pair ; auto with coc.
  apply conv_conv_sum ; auto with coc.
  
  intuition ; try apply type_pi1 with B ; auto with coc.

  intuition ; try apply type_pi1 with B ; auto with coc.
  apply type_pair with s1 s2 s3 ; auto with coc.

  intuition ; try apply type_pi2 with A ; auto with coc.
  destruct (type_sorted H) ; try discriminate.
  destruct H1.
  destruct (generation_sum2 H1).
  intuition.
  assert(e |- Pi1 t : A) by apply type_pi1 with B ; auto with coc.
  assert(e |- Pi1 t' : A) by apply type_pi1 with B ; auto with coc.
  pose (substitution H5 H4).
  pose (substitution H5 H7).

  apply type_conv with (subst (Pi1 t') B) x ; auto with coc.
  apply type_pi2 with A ; auto with coc.
  apply conv_coerce ; auto with coc.
  unfold subst ; apply conv_conv_subst ; auto with coc.
  
  intuition ; try apply type_pi2 with A ; auto with coc.
  assert(e |- Pair (Sum A B) u v : Sum A B) by  apply type_pair with s1 s2 s3 ; auto with coc.
  assert(e |- Pi1 (Pair (Sum A B) u v) : A) by apply type_pi1 with B ; auto.
  pose (substitution H0 H1).
  apply type_conv with (subst (Pi1 (Pair (Sum A B) u v)) B) s2 ; auto with coc.
  apply type_pi2 with A ; auto with coc.
  change (Srt s2) with (subst (Pi1 (Pair (Sum A B) u v)) (Srt s2)).
  apply substitution with A ; auto with coc.
  apply conv_coerce ; auto with coc.
  change (Srt s2) with (subst (Pi1 (Pair (Sum A B) u v)) (Srt s2)).
  apply substitution with A ; auto with coc.
  unfold subst ; apply conv_conv_subst ; auto with coc.

  intuition ; try apply type_subset ; auto with coc.
  apply typ_conv_env with (A :: e) ; auto with coc.
  apply coerce_env_hd with set ; auto with coc.
  apply wf_var with set ; auto.
  apply conv_conv_subset ; auto.

  intuition.
  
  intuition.
  apply trans_conv_conv with N ; auto.

  intuition.
  apply type_conv with A s ; auto.
  apply type_conv with A s ; auto.
Qed.

Corollary type_jrussell_to_russell : forall G t T, JRussell.Types.typ G t T -> G |- t : T.
Proof (proj1 (jrussell_to_russell)).

Corollary coerce_jrussell_to_russell : forall G U V s, 
   JRussell.Types.coerce G U V s -> G |- U >> V : s.
Proof.
  intros.
  destruct (jrussell_to_russell).
  destruct H1.
  pose (H1 _ _ _ _ H).
  intuition.
Qed.

Corollary jeq_jrussell_to_russell : forall G u v T, G |- u = v : T -> 
  G |- u : T /\ G |- v : T /\ conv u v.
Proof.
  intros.
  destruct (jrussell_to_russell).
  destruct H1.
  pose (H2 _ _ _ _ H).
  intuition.
Qed.
