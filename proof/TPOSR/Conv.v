Require Import TPOSR.Terms.
Require Import TPOSR.LiftSubst.
Require Import TPOSR.Reduction.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : lterm.

Section Church_Rosser.

  Definition str_confluent (R : lterm -> lterm -> Prop) :=
    commut _ R (transp _ R).

  Lemma str_confluence_par_lred1 : str_confluent par_lred1.
red ; red.
intros x y H ; induction H ; intros.
inversion_clear H1.
elim IHpar_lred1_1 with M'0; auto with coc core arith sets; intros.
elim IHpar_lred1_2 with N'0; auto with coc core arith sets; intros.
exists (lsubst x0 x); unfold lsubst in |- *; auto with coc core arith sets.

inversion_clear H3.
elim IHpar_lred1_1 with M'1; auto with coc core arith sets; intros.
elim IHpar_lred1_2 with N'0; auto with coc core arith sets; intros.
exists (lsubst x0 x); auto with coc core arith sets; unfold lsubst in |- *;
 auto with coc core arith sets.

inversion_clear H0.
apply IHpar_lred1 ; auto.

unfold transp.
inversion_clear H1.
unfold transp.
induction (IHpar_lred1 M'1).
exists x ;  auto with coc core arith sets.
assumption.

inversion_clear H0.
apply IHpar_lred1 ; auto.

inversion_clear H1.
induction (IHpar_lred1 N'0).
exists x ;  auto with coc core arith sets.
assumption.

inversion_clear H.
exists (Srt_l s); auto with coc core arith sets.

inversion_clear H.
exists (Ref_l n); auto with coc core arith sets.

inversion_clear H1.
elim IHpar_lred1_1 with M'0; auto with coc core arith sets; intros.
elim IHpar_lred1_2 with T'0; auto with coc core arith sets; intros.
exists (Abs_l x0 x); auto with coc core arith sets.

generalize H0 IHpar_lred1_2.
clear H0 IHpar_lred1_2.
inversion_clear H2.
intro.
inversion_clear H2.
intros.
elim IHpar_lred1_1 with T'; auto with coc core arith sets; intros.
elim IHpar_lred1_2 with (Abs_l T'0 M'0); auto with coc core arith sets; intros.
elim IHpar_lred1_3 with N'0; auto with coc core arith sets; intros.

apply inv_par_lred_abs with T'0 M'0 x0; intros; auto with coc core arith sets.
generalize H7 H8.
rewrite H11.
clear H7 H8; intros.
inversion_clear H7.
inversion_clear H8.
exists (lsubst x1 U'); auto with coc core arith sets.
unfold lsubst in |- *; auto with coc core arith sets.

intros.
elim IHpar_lred1_1 with T'0; auto with coc core arith sets; intros.
elim IHpar_lred1_2 with M'0; auto with coc core arith sets; intros.
elim IHpar_lred1_3 with N'0; auto with coc core arith sets; intros.
exists (App_l x x0 x1); auto with coc core arith sets.

intros.
inversion_clear H2.
elim IHpar_lred1_1 with T'0; auto with coc core arith sets; intros.
elim IHpar_lred1_2 with M'0; auto with coc core arith sets; intros.
elim IHpar_lred1_3 with N'0; auto with coc core arith sets; intros.
exists (Pair_l x x0 x1); auto with coc core arith sets.

intros.
inversion_clear H1.
elim IHpar_lred1_1 with M'0; auto with coc core arith sets; intros.
elim IHpar_lred1_2 with N'0; auto with coc core arith sets; intros.
exists (Prod_l x x0); auto with coc core arith sets.


intros.
inversion_clear H1.
elim IHpar_lred1_1 with M'0; auto with coc core arith sets; intros.
elim IHpar_lred1_2 with N'0; auto with coc core arith sets; intros.
exists (Sum_l x x0); auto with coc core arith sets.


intros.
inversion_clear H1.
elim IHpar_lred1_1 with M'0; auto with coc core arith sets; intros.
elim IHpar_lred1_2 with N'0; auto with coc core arith sets; intros.
exists (Subset_l x x0); auto with coc core arith sets.

generalize H IHpar_lred1.
clear H IHpar_lred1.
inversion_clear H0.
intro.
inversion_clear H0.
intros.
elim IHpar_lred1 with (Pair_l T' z N') ; auto with coc core arith sets; intros.
apply inv_par_lred_pair with T' z N' x; intros; auto with coc core arith sets.
generalize H0 H4.
rewrite H5.
clear H0 H4 ; intros.
inversion_clear H0.
inversion_clear H4.
exists U' ; auto with coc core arith sets.

intros.
elim IHpar_lred1 with M'0.
intros.
exists (Pi1_l x) ; auto with coc core arith sets.
assumption.


generalize H IHpar_lred1.
clear H IHpar_lred1.
inversion_clear H0.
intro.
inversion_clear H0.
intros.
elim IHpar_lred1 with (Pair_l T' M'0 z) ; auto with coc core arith sets; intros.
apply inv_par_lred_pair with T' M'0 z x; intros; auto with coc core arith sets.
generalize H0 H4.
rewrite H5.
clear H0 H4 ; intros.
inversion_clear H0.
inversion_clear H4.
exists V' ; auto with coc core arith sets.

intros.
elim IHpar_lred1 with M'0.
intros.
exists (Pi2_l x) ; auto with coc core arith sets.
assumption.

intros.
inversion_clear H1.
elim IHpar_lred1_1 with M'0; auto with coc core arith sets; intros.
elim IHpar_lred1_2 with N'0; auto with coc core arith sets; intros.
exists (Let_in_l x x0); auto with coc core arith sets.
Qed.

  Lemma strip_lemma : commut _ par_lred (transp _ par_lred1).
unfold commut, par_lred in |- *; simple induction 1; intros.
elim str_confluence_par_lred1 with z x0 y0; auto with coc core arith sets;
 intros.
exists x1; auto with coc core arith sets.

elim H1 with z0; auto with coc core arith sets; intros.
elim H3 with x1; intros; auto with coc core arith sets.
exists x2; auto with coc core arith sets.
apply t_trans with x1; auto with coc core arith sets.
Qed.


  Lemma confluence_par_lred : str_confluent par_lred.
red in |- *; red in |- *.
simple induction 1; intros.
elim strip_lemma with z x0 y0; intros; auto with coc core arith sets.
exists x1; auto with coc core arith sets.

elim H1 with z0; intros; auto with coc core arith sets.
elim H3 with x1; intros; auto with coc core arith sets.
exists x2; auto with coc core arith sets.
red in |- *.
apply t_trans with x1; auto with coc core arith sets.
Qed.


  Lemma confluence_lred : str_confluent lred.
red in |- *; red in |- *.
intros.
elim confluence_par_lred with x y z; auto with coc core arith sets; intros.
exists x0; auto with coc core arith sets.
Qed.


  Theorem church_rosser :
   forall u v, conv u v -> ex2 (fun t => lred u t) (fun t => lred v t).
simple induction 1; intros.
exists u; auto with coc core arith sets.

elim H1; intros.
elim confluence_lred with x P N; auto with coc core arith sets; intros.
exists x0; auto with coc core arith sets.
apply trans_lred_lred with x; auto with coc core arith sets.

elim H1; intros.
exists x; auto with coc core arith sets.
apply trans_lred_lred with P; auto with coc core arith sets.
Qed.



  Lemma inv_conv_prod_l :
   forall a b c d : lterm, conv (Prod_l a c) (Prod_l b d) -> conv a b.
intros.
elim church_rosser with (Prod_l a c) (Prod_l b d); intros;
 auto with coc core arith sets.
apply lred_prod_prod with a c x; intros; auto with coc core arith sets.
apply lred_prod_prod with b d x; intros; auto with coc core arith sets.
apply trans_conv_conv with a0; auto with coc core arith sets.
apply sym_conv.
generalize H2.
rewrite H5; intro.
injection H8.
simple induction 2; auto with coc core arith sets.
Qed.

  Lemma inv_conv_prod_r :
   forall a b c d : lterm, conv (Prod_l a c) (Prod_l b d) -> conv c d.
intros.
elim church_rosser with (Prod_l a c) (Prod_l b d); intros;
 auto with coc core arith sets.
apply lred_prod_prod with a c x; intros; auto with coc core arith sets.
apply lred_prod_prod with b d x; intros; auto with coc core arith sets.
apply trans_conv_conv with b0; auto with coc core arith sets.
apply sym_conv.
generalize H2.
rewrite H5; intro.
injection H8.
simple induction 1; auto with coc core arith sets.
Qed.

  Lemma inv_conv_sum_l :
   forall a b c d : lterm, conv (Sum_l a c) (Sum_l b d) -> conv a b.
intros.
elim church_rosser with (Sum_l a c) (Sum_l b d); intros;
 auto with coc core arith sets.
apply lred_sum_sum with a c x; intros; auto with coc core arith sets.
apply lred_sum_sum with b d x; intros; auto with coc core arith sets.
apply trans_conv_conv with a0; auto with coc core arith sets.
apply sym_conv.
generalize H2.
rewrite H5; intro.
injection H8.
simple induction 2; auto with coc core arith sets.
Qed.


Lemma inv_conv_sum_r :
   forall a b c d : lterm, conv (Sum_l a c) (Sum_l b d) -> conv c d.
intros.
elim church_rosser with (Sum_l a c) (Sum_l b d); intros;
 auto with coc core arith sets.
apply lred_sum_sum with a c x; intros; auto with coc core arith sets.
apply lred_sum_sum with b d x; intros; auto with coc core arith sets.
apply trans_conv_conv with b0; auto with coc core arith sets.
apply sym_conv.
generalize H2.
rewrite H5; intro.
injection H8.
simple induction 1; auto with coc core arith sets.
Qed.


Lemma inv_conv_subset_l :
   forall a b c d : lterm, conv (Subset_l a c) (Subset_l b d) -> conv a b.
intros.
elim church_rosser with (Subset_l a c) (Subset_l b d); intros;
 auto with coc core arith sets.
apply lred_subset_subset with a c x; intros; auto with coc core arith sets.
apply lred_subset_subset with b d x; intros; auto with coc core arith sets.
apply trans_conv_conv with a0; auto with coc core arith sets.
apply sym_conv.
generalize H2.
rewrite H5; intro.
injection H8.
simple induction 2; auto with coc core arith sets.
Qed.


Lemma inv_conv_subset_r :
   forall a b c d : lterm, conv (Subset_l a c) (Subset_l b d) -> conv c d.
intros.
elim church_rosser with (Subset_l a c) (Subset_l b d); intros;
 auto with coc core arith sets.
apply lred_subset_subset with a c x; intros; auto with coc core arith sets.
apply lred_subset_subset with b d x; intros; auto with coc core arith sets.
apply trans_conv_conv with b0; auto with coc core arith sets.
apply sym_conv.
generalize H2.
rewrite H5; intro.
injection H8.
simple induction 1; auto with coc core arith sets.
Qed.



  Lemma nf_uniqueness : forall u v, conv u v -> normal u -> normal v -> u = v. 
intros.
elim church_rosser with u v; intros; auto with coc core arith sets.
rewrite (lred_normal u x); auto with coc core arith sets.
elim lred_normal with v x; auto with coc core arith sets.
Qed.


  Lemma conv_sort : forall s1 s2, conv (Srt_l s1) (Srt_l s2) -> s1 = s2.
intros.
cut (Srt_l s1 = Srt_l s2); intros.
injection H0; auto with coc core arith sets.

apply nf_uniqueness; auto with coc core arith sets.
red in |- *; red in |- *; intros.
inversion_clear H0.

red in |- *; red in |- *; intros.
inversion_clear H0.
Qed.


  Lemma conv_kind_prop : ~ conv (Srt_l kind) (Srt_l prop).
red in |- *; intro.
absurd (kind = prop).
discriminate.

apply conv_sort; auto with coc core arith sets.
Qed.

  Lemma conv_kind_set : ~ conv (Srt_l kind) (Srt_l set).
red in |- *; intro.
absurd (kind = set).
discriminate.

apply conv_sort; auto with coc core arith sets.
Qed.

Lemma conv_sort_ref : forall s n, ~ conv (Srt_l s) (Ref_l n).
red in |- *; intros.
elim church_rosser with (Srt_l s) (Ref_l n); auto with coc core arith sets.
do 2 intro.
elim lred_normal with (Srt_l s) x; auto with coc core arith sets.
intro.
apply lred_ref_ref with n (Srt_l s); auto with coc core arith sets; intros.
unfold not ; intros ; discriminate H2.

red in |- *; red in |- *; intros.
inversion_clear H1.
Qed.


  Lemma conv_sort_prod : forall s t u, ~ conv (Srt_l s) (Prod_l t u).
red in |- *; intros.
elim church_rosser with (Srt_l s) (Prod_l t u); auto with coc core arith sets.
do 2 intro.
elim lred_normal with (Srt_l s) x; auto with coc core arith sets.
intro.
apply lred_prod_prod with t u (Srt_l s); auto with coc core arith sets; intros.
discriminate H2.

red in |- *; red in |- *; intros.
inversion_clear H1.
Qed.

  Lemma conv_sort_sum : forall s t u, ~ conv (Srt_l s) (Sum_l t u).
red in |- *; intros.
elim church_rosser with (Srt_l s) (Sum_l t u); auto with coc core arith sets.
do 2 intro.
elim lred_normal with (Srt_l s) x; auto with coc core arith sets.
intro.
apply lred_sum_sum with t u (Srt_l s); auto with coc core arith sets; intros.
discriminate H2.

red in |- *; red in |- *; intros.
inversion_clear H1.
Qed.

  Lemma conv_sort_subset : forall s t u, ~ conv (Srt_l s) (Subset_l t u).
red in |- *; intros.
elim church_rosser with (Srt_l s) (Subset_l t u); auto with coc core arith sets.
do 2 intro.
elim lred_normal with (Srt_l s) x; auto with coc core arith sets.
intro.
apply lred_subset_subset with t u (Srt_l s); auto with coc core arith sets; intros.
discriminate H2.

red in |- *; red in |- *; intros.
inversion_clear H1.
Qed.

  Lemma conv_prod_subset : forall U V t u, ~ conv (Prod_l U V) (Subset_l t u).
red in |- *; intros.
elim church_rosser with (Prod_l U V) (Subset_l t u); auto with coc core arith sets.
intros.

inversion H0 ; inversion H1.
rewrite <- H3 in H2 ; discriminate.

apply lred_subset_subset with t u P ; auto with coc core.
intros.
rewrite H6 in H4.
rewrite <- H2 in H4.
inversion H4.

apply lred_prod_prod with U V P ; auto with coc core.
intros.
rewrite H6 in H3.
rewrite <- H5 in H3.
inversion H3.

apply lred_prod_prod with U V P ; auto with coc core ; intros.
apply lred_subset_subset with t u P0 ; auto with coc core ; intros.
rewrite H11 in H6.
rewrite H8 in H3.

inversion H6.
rewrite <- H15 in H3.
inversion H3.

rewrite <- H15 in H3.
inversion H3.
Qed.

  Lemma conv_prod_sum : forall U V t u, ~ conv (Prod_l U V) (Sum_l t u).
red in |- *; intros.
elim church_rosser with (Prod_l U V) (Sum_l t u); auto with coc core arith sets.
intros.

inversion H0 ; inversion H1.
rewrite <- H3 in H2 ; discriminate.

apply lred_sum_sum with t u P ; auto with coc core.
intros.
rewrite H6 in H4.
rewrite <- H2 in H4.
inversion H4.

apply lred_prod_prod with U V P ; auto with coc core.
intros.
rewrite H6 in H3.
rewrite <- H5 in H3.
inversion H3.

apply lred_prod_prod with U V P ; auto with coc core ; intros.
apply lred_sum_sum with t u P0 ; auto with coc core ; intros.
rewrite H11 in H6.
rewrite H8 in H3.

inversion H6.
rewrite <- H15 in H3.
inversion H3.

rewrite <- H15 in H3.
inversion H3.
Qed.

  Lemma conv_subset_sum : forall U V t u, ~ conv (Subset_l U V) (Sum_l t u).
red in |- *; intros.
elim church_rosser with (Subset_l U V) (Sum_l t u); auto with coc core arith sets.
intros.

inversion H0 ; inversion H1.
rewrite <- H3 in H2 ; discriminate.

apply lred_sum_sum with t u P ; auto with coc core.
intros.
rewrite H6 in H4.
rewrite <- H2 in H4.
inversion H4.

apply lred_subset_subset with U V P ; auto with coc core.
intros.
rewrite H6 in H3.
rewrite <- H5 in H3.
inversion H3.

apply lred_subset_subset with U V P ; auto with coc core ; intros.
apply lred_sum_sum with t u P0 ; auto with coc core ; intros.
rewrite H11 in H6.
rewrite H8 in H3.

inversion H6.
rewrite <- H15 in H3.
inversion H3.

rewrite <- H15 in H3.
inversion H3.
Qed.


End Church_Rosser.
