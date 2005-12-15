Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import CCP.Types.

Lemma coerce_conv_coerce : forall U U' V V', conv U U' -> conv V V' ->
  U >> V -> U' >> V'.
Proof.
intros.
induction H1 ; auto with coc core.
apply coerce_conv.
apply trans_conv_conv with A ; auto with coc.
apply trans_conv_conv with B ; auto with coc.

apply coerce_trans with (Prod A' B') ; auto with coc core.
apply coerce_trans with (Prod A B) ; auto with coc core.

apply coerce_trans with (Sum A' B') ; auto with coc core.
apply coerce_trans with (Sum A B) ; auto with coc core.

apply coerce_trans with (Subset U P) ; auto with coc core.
apply coerce_sub_l ; auto with coc core.
apply coerce_trans with U'0 ; auto with coc core.

apply coerce_trans with (Subset U'0 P) ; auto with coc core.
apply coerce_sub_r ; auto with coc core.
apply coerce_trans with U ; auto with coc core.

apply coerce_trans with A ; auto with coc core.
apply coerce_trans with B ; auto with coc core.
apply coerce_trans with C ; auto with coc core.
Qed.

Lemma conv_sym : forall U V, U >> V -> V >> U.
Proof.
intros.
induction H ; auto with coc.

apply coerce_trans with B ; auto with coc.
Qed.

Lemma coerce_kind : forall G U s, G |- U : s -> G |- 
  U >> (Srt kind) -> conv U (Srt kind).
Proof.
intros.
inversion H0 ; auto with coc core.
rewrite <- H2 in H.
inversion H.
rewrite <- H4 in H7.




Lemma coerce_sort_prod : forall s t u, ~ ((Srt s) >> (Prod t u)).
red in |- *; intros.
inversion H.
elim conv_sort_prod with s t u ; auto with coc.

inversion H0.




elim church_rosser with (Srt s) (Prod t u); auto with coc core arith sets.
do 2 intro.
elim red_normal with (Srt s) x; auto with coc core arith sets.
intro.
apply red_prod_prod with t u (Srt s); auto with coc core arith sets; intros.
discriminate H2.

red in |- *; red in |- *; intros.
inversion_clear H1.
inversion H ; auto with coc.



Qed.
