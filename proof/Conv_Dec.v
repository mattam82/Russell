
Require Import Peano_dec.
Require Import Transitive_Closure.
Require Import Union.
Require Import Termes.
Require Import Reduction.

Require Import Conv.

  Definition ord_norm1 := union _ subterm (transp _ red1).
  Definition ord_norm := clos_trans _ ord_norm1.

  Hint Unfold ord_norm1 ord_norm: coc.


  Lemma subterm_ord_norm : forall a b : term, subterm a b -> ord_norm a b.
auto 10 with coc v62.
Qed.

  Hint Resolve subterm_ord_norm: coc.


  Lemma red_red1_ord_norm :
   forall a b : term, red a b -> forall c : term, red1 b c -> ord_norm c a.
red in |- *.
simple induction 1; intros; auto with coc v62.
apply t_trans with N; auto with coc v62.
Qed.



  Lemma wf_subterm : well_founded subterm.
red in |- *.
simple induction a; intros; apply Acc_intro; intros ; 
try (inversion_clear H1; inversion_clear H2; auto with coc v62).
inversion_clear H; inversion_clear H0.

inversion_clear H; inversion_clear H0.

inversion_clear H1.
inversion_clear H1 ; auto.
apply Acc_intro.
assumption.

inversion_clear H0 ; inversion_clear H1 ; auto.

inversion_clear H0 ; inversion_clear H1 ; auto.
Qed.


  Lemma wf_ord_norm1 : forall t : term, sn t -> Acc ord_norm1 t.
unfold ord_norm1 in |- *.
intros.
apply Acc_union; auto with coc v62.
exact commut_red1_subterm.

intros.
apply wf_subterm.
Qed.


  Theorem wf_ord_norm : forall t : term, sn t -> Acc ord_norm t.
unfold ord_norm in |- *.
intros.
apply Acc_clos_trans.
apply wf_ord_norm1; auto with coc v62.
Qed.




  Definition norm_body (a : term) (norm : term -> term) :=
    match a with
    | Srt s => Srt s
    | Ref n => Ref n
    | Abs T t => Abs (norm T) (norm t)
    | App u v =>
        match norm u return term with
        | Abs _ b => norm (subst (norm v) b)
        | t => App t (norm v)
        end
    | Pair T u v => Pair (norm T) (norm u) (norm v)
    | Prod T U => Prod (norm T) (norm U)
    | Sum T U => Sum (norm T) (norm U)
    | Subset T U => Subset (norm T) (norm U)
    | Pi1 t => match (norm t) return term with
      | Pair _ u _ => u
      | t => Pi1 t
      end
    | Pi2 t => match norm t return term with
      | Pair _ _ v => v
      | t => Pi2 t
       end
    | Let_in u v => norm (subst (norm u) v)
    end.

  Theorem compute_nf :
   forall t : term, sn t -> {u : term | red t u &  normal u}.
intros.
elimtype (Acc ord_norm t).
clear t H.
intros [s| n| T t| a b| T a b | T U | T U | T U | t | t | v t] _ norm_rec. 
exists (Srt s); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.

exists (Ref n); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.

elim norm_rec with T ; auto with coc ; try intros T' redT nT.
elim norm_rec with t; auto with coc; intros t' redt nt.
exists (Abs T' t'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nT with M'; trivial.
elim nt with M'; trivial.

elim norm_rec with b; auto with coc; intros v' redv nv.
elim norm_rec with a; auto with coc.
intros [s| n| T t| u v| T u v | T U | T U | T U | t | t | v t] redu nu. 

exists (App (Srt s) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
inversion_clear H0.
elim nv with N2; trivial.

exists (App (Ref n) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
inversion_clear H0.
elim nv with N2; trivial.

elim norm_rec with (subst v' t).
intros t' redt nt.
exists t'; trivial.
apply trans_red_red with (subst v' t); auto with coc.
apply trans_red with (App (Abs T t) v'); auto with coc.

apply red_red1_ord_norm with (App (Abs T t) v'); auto with coc.

exists (App (App u v) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App (Pair T u v) v') ; auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App (Prod T U) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App (Sum T U) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App (Subset T U) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App (Pi1 t) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App (Pi2 t) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App (Let_in v t) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nu with N1; trivial.
elim nv with N2; trivial.

elim norm_rec with T ; auto with coc core ; intros T' redT' nT'.
elim norm_rec with a ; auto with coc core ; intros a' reda' na'.
elim norm_rec with b ; auto with coc core ; intros b' redb' nb'.
exists (Pair T' a' b') ; auto with coc core.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nT' with S; trivial.
elim na' with N1; trivial.
elim nb' with N2; trivial.

elim norm_rec with T; auto with coc; intros T' redT nT.
elim norm_rec with U; auto with coc; intros U' redU nU.
exists (Prod T' U'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nT with N1; trivial.
elim nU with N2; trivial.

elim norm_rec with T; auto with coc; intros T' redT nT.
elim norm_rec with U; auto with coc; intros U' redU nU.
exists (Sum T' U'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nT with N1; trivial.
elim nU with N2; trivial.

elim norm_rec with T; auto with coc; intros T' redT nT.
elim norm_rec with U; auto with coc; intros U' redU nU.
exists (Subset T' U'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nT with N1; trivial.
elim nU with N2; trivial.

elim norm_rec with t; auto with coc.
intros [s| n| T t'| u v| T u v | T U | T U | T U | t' | t' | v t'] redu nu. 

exists (Pi1 (Srt s)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi1 (Ref n)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi1 (Abs T t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi1 (App u v)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists u; auto with coc.
apply trans_red with (Pi1 (Pair T u v)) ; auto with coc core.
red in |- *; red in |- *; intros.
unfold normal in nu.
elim nu with (Pair T u0 v); auto with coc core.

exists (Pi1 (Prod T U)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi1 (Sum T U)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi1 (Subset T U)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi1 (Pi1 t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi1 (Pi2 t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi1 (Let_in v t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

elim norm_rec with t; auto with coc.
intros [s| n| T t'| u v| T u v | T U | T U | T U | t' | t' | v t'] redu nu. 

exists (Pi2 (Srt s)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi2 (Ref n)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi2 (Abs T t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi2 (App u v)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists v; auto with coc.
apply trans_red with (Pi2 (Pair T u v)) ; auto with coc core.
red in |- *; red in |- *; intros.
unfold normal in nu.
elim nu with (Pair T u u0); auto with coc core.

exists (Pi2 (Prod T U)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi2 (Sum T U)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi2 (Subset T U)); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi2 (Pi1 t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi2 (Pi2 t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

exists (Pi2 (Let_in v t')); auto with coc ; red in |- *; red in |- *; intros.
inversion_clear H ; auto with coc core ;
elim nu with N; trivial.

elim norm_rec with v ;  auto with coc ; intros v' redv nv.
elim norm_rec with t ;  auto with coc ; intros t' redt nt.
exists (Let_in v' t') ; auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nv with N1; trivial.
elim nt with N2; trivial.

apply wf_ord_norm; auto with coc.
Qed.

  Lemma eqterm : forall u v : term, {u = v} + {u <> v}.
Proof.
decide equality.
decide equality s s0.
apply eq_nat_dec.
Qed.

  Theorem is_conv :
   forall u v : term, sn u -> sn v -> {conv u v} + {~ conv u v}.
Proof.
intros u v snu snv.
elim compute_nf with (1 := snu); intros u' redu nu.
elim compute_nf with (1 := snv); intros v' redv nv.
elim eqterm with u' v'; [ intros same_nf | intros diff_nf ].
left.
apply trans_conv_conv with u'; auto with coc.
rewrite same_nf; apply sym_conv; auto with coc.

right; red in |- *; intro; apply diff_nf.
elim church_rosser with u' v'; auto with coc; intros.
rewrite (red_normal u' x); auto with coc.
rewrite (red_normal v' x); auto with coc.

apply trans_conv_conv with v; auto with coc.
apply trans_conv_conv with u; auto with coc.
apply sym_conv; auto with coc.
Qed.