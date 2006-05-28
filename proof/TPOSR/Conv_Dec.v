Require Import Peano_dec.
Require Import Transitive_Closure.
Require Import Union.
Require Import Lambda.TPOSR.Terms.
Require Import Lambda.TPOSR.Reduction.
Require Import Lambda.TPOSR.Conv.

  Definition ord_norm1 := union _ sublterm (transp _ lred1).
  Definition ord_norm := clos_trans _ ord_norm1.

  Hint Unfold ord_norm1 ord_norm: coc.


  Lemma sublterm_ord_norm : forall a b : lterm, sublterm a b -> ord_norm a b.
auto 10 with coc v62.
Qed.

  Hint Resolve sublterm_ord_norm: coc.


  Lemma lred_lred1_ord_norm :
   forall a b : lterm, lred a b -> forall c : lterm, lred1 b c -> ord_norm c a.
red in |- *.
simple induction 1; intros; auto with coc v62.
apply t_trans with N; auto with coc v62.
Qed.



  Lemma wf_sublterm : well_founded sublterm.
red in |- *.
simple induction a; intros; apply Acc_intro; intros ; 
try (inversion_clear H1; inversion_clear H2; auto with coc v62).
inversion_clear H; inversion_clear H0.

inversion_clear H; inversion_clear H0.

inversion_clear H1.
inversion_clear H1 ; auto.
apply Acc_intro.
assumption.

inversion_clear H1.
inversion_clear H1 ; auto.
apply Acc_intro.
assumption.
Qed.


  Lemma wf_ord_norm1 : forall t : lterm, sn t -> Acc ord_norm1 t.
unfold ord_norm1 in |- *.
intros.
apply Acc_union; auto with coc v62.
exact commut_lred1_sublterm.

intros.
apply wf_sublterm.
Qed.


  Theorem wf_ord_norm : forall t : lterm, sn t -> Acc ord_norm t.
unfold ord_norm in |- *.
intros.
apply Acc_clos_trans.
apply wf_ord_norm1; auto with coc v62.
Qed.




  Definition norm_body (a : lterm) (norm : lterm -> lterm) :=
    match a with
    | Srt_l s => Srt_l s
    | Ref_l n => Ref_l n
    | Abs_l T t => Abs_l (norm T) (norm t)
    | App_l T u v =>
        match norm u return lterm with
        | Abs_l _ b => norm (lsubst (norm v) b)
        | t => App_l (norm T) t (norm v)
        end
    | Pair_l T u v => Pair_l (norm T) (norm u) (norm v)
    | Prod_l T U => Prod_l (norm T) (norm U)
    | Sum_l T U => Sum_l (norm T) (norm U)
    | Subset_l T U => Subset_l (norm T) (norm U)
    | Pi1_l T t => match (norm t) return lterm with
      | Pair_l _ u _ => u
      | t => Pi1_l (norm T) t
      end
    | Pi2_l T t => match norm t return lterm with
      | Pair_l _ _ v => v
      | t => Pi2_l (norm T) t
       end
    end.

  Theorem compute_nf :
   forall t : lterm, sn t -> {u : lterm | lred t u &  normal u}.
intros.
elimtype (Acc ord_norm t).
clear t H.
intros [s| n| T t| Typ a b| T a b | T U | T U | T U | Typ t | Typ t] _ norm_rec. 
exists (Srt_l s); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.

exists (Ref_l n); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.

elim norm_rec with T ; auto with coc ; try intros T' lredT nT.
elim norm_rec with t; auto with coc; intros t' lredt nt.
exists (Abs_l T' t'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nT with M'; trivial.
elim nt with M'; trivial.

elim norm_rec with b; auto with coc; intros v' lredv nv.
elim norm_rec with a; auto with coc.
elim norm_rec with Typ; auto with coc; intros Typ'' lredTyp nTyp.
intros [s| n| T t| Typ' u v| T u v | T U | T U | T U | Typpi1 t | Typpi2 t] lredu nu. 

exists (App_l Typ'' (Srt_l s) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nTyp with S; trivial.
inversion_clear H0.
elim nv with N2; trivial.

exists (App_l Typ'' (Ref_l n) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nTyp with S; trivial.
inversion_clear H0.
elim nv with N2; trivial.

elim norm_rec with (lsubst v' t).
intros t' lredt nt.
exists t'; trivial.
apply trans_lred_lred with (lsubst v' t); auto with coc.
apply trans_lred with (App_l Typ (Abs_l T t) v'); auto with coc.

apply lred_lred1_ord_norm with (App_l Typ (Abs_l T t) v'); auto with coc.

exists (App_l Typ'' (App_l Typ' u v) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nTyp with S; trivial.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App_l Typ'' (Pair_l T u v) v') ; auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nTyp with S; trivial.

elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App_l Typ'' (Prod_l T U) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nTyp with S; trivial.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App_l Typ'' (Sum_l T U) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nTyp with S; trivial.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App_l Typ'' (Subset_l T U) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nTyp with S; trivial.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App_l Typ'' (Pi1_l Typpi1 t) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nTyp with S; trivial.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App_l Typ'' (Pi2_l Typpi2 t) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nTyp with S; trivial.
elim nu with N1; trivial.
elim nv with N2; trivial.

elim norm_rec with T ; auto with coc core ; intros T' lredT' nT'.
elim norm_rec with a ; auto with coc core ; intros a' lreda' na'.
elim norm_rec with b ; auto with coc core ; intros b' lredb' nb'.
exists (Pair_l T' a' b') ; auto with coc core.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nT' with S; trivial.
elim na' with N1; trivial.
elim nb' with N2; trivial.

elim norm_rec with T; auto with coc; intros T' lredT nT.
elim norm_rec with U; auto with coc; intros U' lredU nU.
exists (Prod_l T' U'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nT with N1; trivial.
elim nU with N2; trivial.

elim norm_rec with T; auto with coc; intros T' lredT nT.
elim norm_rec with U; auto with coc; intros U' lredU nU.
exists (Sum_l T' U'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nT with N1; trivial.
elim nU with N2; trivial.

elim norm_rec with T; auto with coc; intros T' lredT nT.
elim norm_rec with U; auto with coc; intros U' lredU nU.
exists (Subset_l T' U'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nT with N1; trivial.
elim nU with N2; trivial.

elim norm_rec with Typ; auto with coc; intros Typ'' lredTyp nTyp.
elim norm_rec with t; auto with coc.
intros [s| n| T t'| T u v| T u v | T U | T U | T U | Typpi1 t' | Typpi2 t'] lredu nu. 

exists (Pi1_l Typ'' (Srt_l s)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H.
elim nTyp with N; trivial.
elim nu with N; trivial.

exists (Pi1_l Typ'' (Ref_l n)); auto with coc ; red in |- *; red in |- *; intros.

inversion_clear H ; auto with coc core ; elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi1_l Typ'' (Abs_l T t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ; elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi1_l Typ'' (App_l T u v)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ; elim nTyp with N; trivial ;
elim nu with N; trivial.

exists u; auto with coc.
apply trans_lred with (Pi1_l Typ'' (Pair_l T u v)) ; auto with coc core.
red in |- *; red in |- *; intros.
unfold normal in nu.
elim nu with (Pair_l T u0 v); auto with coc core.

exists (Pi1_l Typ''  (Prod_l T U)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi1_l Typ'' (Sum_l T U)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi1_l Typ'' (Subset_l T U)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi1_l Typ'' (Pi1_l Typpi1 t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi1_l Typ'' (Pi2_l Typpi2 t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

elim norm_rec with Typ; auto with coc ; intros Typ' lredTyp nTyp.
elim norm_rec with t; auto with coc.

intros [s| n| T t'| T u v| T u v | T U | T U | T U | Tpi t' | Tpi t'] lredu nu. 

exists (Pi2_l Typ' (Srt_l s)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi2_l Typ' (Ref_l n)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi2_l Typ' (Abs_l T t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi2_l Typ' (App_l T u v)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

exists v; auto with coc.
apply trans_lred with (Pi2_l Typ' (Pair_l T u v)) ; auto with coc core.
red in |- *; red in |- *; intros.
unfold normal in nu.
elim nu with (Pair_l T u u0); auto with coc core.

exists (Pi2_l Typ' (Prod_l T U)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi2_l Typ' (Sum_l T U)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi2_l Typ' (Subset_l T U)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi2_l Typ' (Pi1_l Tpi t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

exists (Pi2_l Typ' (Pi2_l Tpi t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;elim nTyp with N; trivial ;
elim nu with N; trivial.

apply wf_ord_norm; auto with coc.
Qed.

  Lemma eqlterm : forall u v : lterm, {u = v} + {u <> v}.
Proof.
decide equality.
decide equality s s0.
apply eq_nat_dec.
Qed.

  Theorem is_conv :
   forall u v : lterm, sn u -> sn v -> {conv u v} + {~ conv u v}.
Proof.
intros u v snu snv.
elim compute_nf with (1 := snu); intros u' lredu nu.
elim compute_nf with (1 := snv); intros v' lredv nv.
elim eqlterm with u' v'; [ intros same_nf | intros diff_nf ].
left.
apply trans_conv_conv with u'; auto with coc.
rewrite same_nf; apply sym_conv; auto with coc.

right; red in |- *; intro; apply diff_nf.
elim church_rosser with u' v'; auto with coc; intros.
rewrite (lred_normal u' x); auto with coc.
rewrite (lred_normal v' x); auto with coc.

apply trans_conv_conv with v; auto with coc.
apply trans_conv_conv with u; auto with coc.
apply sym_conv; auto with coc.
Qed.