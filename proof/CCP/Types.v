
Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Export MyList.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

  Definition env := list term.

  Implicit Types e f g : env.

  Definition item_lift t e n :=
    ex2 (fun u => t = lift (S n) u) (fun u => item term u (e:list term) n).



Section Typage.
  Inductive coerce : term -> term -> Prop :=
  | coerce_conv : forall A B, conv A B -> coerce A B
  | coerce_prod : forall A B A' B', coerce A' A -> coerce B B' -> coerce (Prod A B) (Prod A' B')
  | coerce_sum : forall A B A' B', coerce A A' -> coerce B B' -> coerce (Sum A B) (Sum A' B')
  | coerce_sub_l : forall U U' P, coerce U U' -> coerce U (Subset U' P)
  | coerce_sub_r : forall U P U', coerce U U' -> coerce (Subset U P) U'
  | coerce_trans : forall A B C, coerce A B ->  coerce B C -> coerce A C.

Hint Resolve coerce_conv coerce_prod coerce_sum coerce_sub_l coerce_sub_r coerce_trans : CCP.

  Inductive wf : env -> Prop :=
    | wf_nil : wf nil
    | wf_var : forall e T s, typ e T (Srt s) -> wf (T :: e)
with typ : env -> term -> term -> Prop :=
  | type_prop : forall e, wf e -> typ e (Srt prop) (Srt kind)
  | type_set : forall e, wf e -> typ e (Srt set) (Srt kind)
  | type_var :
      forall e,
      wf e -> forall (v : nat) t, item_lift t e v -> typ e (Ref v) t
  | type_abs :
      forall e T s1,
      typ e T (Srt s1) ->
      forall M (U : term) s2,
      typ (T :: e) U (Srt s2) ->
      typ (T :: e) M U -> typ e (Abs T M) (Prod T U)
  | type_app :
      forall e v (V : term),
      typ e v V ->
      forall u (Ur : term),
      typ e u (Prod V Ur) -> typ e (App u v) (subst v Ur)	
  | type_pair :
    forall e (U : term) s1,
      typ e U (Srt s1) ->
      forall u, typ e u U ->
      forall V s2, typ (U :: e) V (Srt s2) ->
	forall v, typ e v (subst u V) -> 
	  typ e (Pair (Sum U V) u v) (Sum U V)
  | type_prod :
      forall e T s1,
      typ e T (Srt s1) ->
      forall (U : term) s2,
      typ (T :: e) U (Srt s2) -> typ e (Prod T U) (Srt s2)
  | type_sum :
      forall e T s1,
      typ e T (Srt s1) ->
      forall (U : term) s2,
      typ (T :: e) U (Srt s2) -> typ e (Sum T U) (Srt s2)

  | type_subset :
      forall e T s1,
      typ e T (Srt set) ->
      forall (U : term),
      typ (T :: e) U (Srt prop) -> typ e (Subset T U) (Srt set)

  | type_pi1 :
      forall e t U V,
      typ e t (Sum U V) -> typ e (Pi1 t) U

  | type_pi2 :
      forall e t U V,
      typ e t (Sum U V) -> typ e (Pi2 t) (subst (Pi1 t) V)

  | type_let_in :
      forall e t U,
      typ e t U ->
      forall s1, typ e U (Srt s1) -> (* Just for easier induction, derivable from the next 
	 judgment *)
      forall v M,
      typ (U :: e) v M -> 
      forall s2, typ (U :: e) M (Srt s2) ->
      typ e (Let_in t v) (subst t M)

  | type_conv :
      forall e t (U V : term),
      typ e t U -> coerce U V -> forall s, typ e V (Srt s) -> typ e t V.

  Hint Resolve wf_nil type_prop type_set type_var: coc.


  Lemma type_prop_set :
   forall s, is_prop s -> forall e, wf e -> typ e (Srt s) (Srt kind).
simple destruct 1; intros; rewrite H0.
apply type_prop; trivial.
apply type_set; trivial.
Qed.


Lemma typ_free_db : forall e t T, typ e t T -> free_db (length e) t.
Proof.
  simple induction 1 ; intros ; auto with coc core arith datatypes.
  inversion_clear H1.
  apply db_ref.
  elim H3; simpl in |- *; intros; auto with coc core arith datatypes.
Qed.


  Lemma typ_wf : forall e t T, typ e t T -> wf e.
simple induction 1; auto with coc core arith datatypes.
Qed.


  Lemma wf_sort :
   forall n e f,
   trunc _ (S n) e f ->
   wf e -> forall t, item _ t e n -> exists s : sort, typ f t (Srt s).
simple induction n.
do 3 intro.
inversion_clear H.
inversion_clear H0.
intros.
inversion_clear H0.
inversion_clear H.
exists s; auto with coc core arith datatypes.

do 5 intro.
inversion_clear H0.
intros.
inversion_clear H2.
inversion_clear H0.
elim H with e0 f t; intros; auto with coc core arith datatypes.
exists x0; auto with coc core arith datatypes.

apply typ_wf with x (Srt s); auto with coc core arith datatypes.
Qed.



  Definition inv_type (P : Prop) e t T : Prop :=
    match t with
    | Srt prop => conv T (Srt kind) -> P
    | Srt set => conv T (Srt kind) -> P
    | Srt kind => True
    | Ref n => forall x : term, item _ x e n -> conv T (lift (S n) x) -> P
    | Abs A M =>
        forall s1 s2 (U : term),
        typ e A (Srt s1) ->
        typ (A :: e) M U -> typ (A :: e) U (Srt s2) -> conv T (Prod A U) -> P
    | App u v =>
        forall Ur V : term,
        typ e v V -> typ e u (Prod V Ur) -> conv T (subst v Ur) -> P
    | Pair T' u v => 
        forall U s1, typ e U (Srt s1) ->
	  typ e u U -> 
	  forall V s2, typ (U :: e) V (Srt s2) ->
            typ e v (subst u V) -> T' = (Sum U V) -> conv T (Sum U V) -> P
    | Prod A B =>
        forall s1 s2,
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) -> conv T (Srt s2) -> P
    | Sum A B =>
        forall s1 s2,
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) -> conv T (Srt s2) -> P
    | Subset A B =>
        forall s1 s2,
        typ e A (Srt set) -> typ (A :: e) B (Srt prop) -> conv T (Srt set) -> P
    | Pi1 t =>
        forall U V,
        typ e t (Sum U V) -> conv T U -> P
    | Pi2 t =>
        forall U V,
        typ e t (Sum U V) -> conv T (subst (Pi1 t) V) -> P
    | Let_in t v =>
        forall U, typ e t U -> 
	forall s1, typ e U (Srt s1) ->
        forall M, typ (U :: e) v M -> 
        forall s2, typ (U :: e) M (Srt s2) ->
        conv T (subst t M) -> P
    end.

  Lemma inv_type_conv :
   forall (P : Prop) e t (U V : term),
   conv U V -> inv_type P e t U -> inv_type P e t V.
do 6 intro.
cut (forall x : term, conv V x -> conv U x).
intro.
case t; simpl in |- *; intros.
generalize H1.
elim s; auto with coc core arith datatypes; intros.

apply H1 with x; auto with coc core arith datatypes.

apply H1 with s1 s2 U0; auto with coc core arith datatypes.

apply H1 with Ur V0; auto with coc core arith datatypes.

apply H1 with U0 s1 V0 s2 ; auto with coc core arith datatypes.

apply H1 with s1 s2; auto with coc core arith datatypes.
apply H1 with s1 s2; auto with coc core arith datatypes.
apply H1; auto with coc core arith datatypes.

apply H1 with U0 V0; auto with coc core arith datatypes.

apply H1 with U0 V0; auto with coc core arith datatypes.

apply H1 with U0 s1 M s2; auto with coc core arith datatypes.

intros.
apply trans_conv_conv with V; auto with coc core arith datatypes.
Qed.

  Theorem typ_inversion :
   forall (P : Prop) e t T, typ e t T -> inv_type P e t T -> P.
simple induction 1; simpl in |- *; intros.
auto with coc core arith datatypes.

auto with coc core arith datatypes.

elim H1; intros.
apply H2 with x; auto with coc core arith datatypes.
rewrite H3; auto with coc core arith datatypes.

apply H6 with s1 s2 U; auto with coc core arith datatypes.

apply H4 with Ur V; auto with coc core arith datatypes.

apply H8 with U s1 V s2; auto with coc core arith datatypes.

apply H4 with s1 s2; auto with coc core arith datatypes.
apply H4 with s1 s2; auto with coc core arith datatypes.
apply H4; auto with coc core arith datatypes.

apply H2 with U V; auto with coc core arith datatypes.
apply H2 with U V; auto with coc core arith datatypes.

apply H8 with U s1 M s2; auto with coc core arith datatypes.

apply H1.
apply inv_type_conv with V; auto with coc core arith datatypes.
Qed.


  Lemma inv_typ_kind : forall e t, ~ typ e (Srt kind) t.
red in |- *; intros.
apply typ_inversion with e (Srt kind) t; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_prop : forall e T, typ e (Srt prop) T -> conv T (Srt kind).
intros.
apply typ_inversion with e (Srt prop) T; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_set : forall e T, typ e (Srt set) T -> conv T (Srt kind).
intros.
apply typ_inversion with e (Srt set) T; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_ref :
   forall (P : Prop) e T n,
   typ e (Ref n) T ->
   (forall U : term, item _ U e n -> conv T (lift (S n) U) -> P) -> P.
intros.
apply typ_inversion with e (Ref n) T; simpl in |- *; intros;
 auto with coc core arith datatypes.
apply H0 with x; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_abs :
   forall (P : Prop) e A M (U : term),
   typ e (Abs A M) U ->
   (forall s1 s2 T,
    typ e A (Srt s1) ->
    typ (A :: e) M T -> typ (A :: e) T (Srt s2) -> conv (Prod A T) U -> P) ->
   P.
intros.
apply typ_inversion with e (Abs A M) U; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with s1 s2 U0; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_app :
   forall (P : Prop) e u v T,
   typ e (App u v) T ->
   (forall V Ur : term,
    typ e u (Prod V Ur) -> typ e v V -> conv T (subst v Ur) -> P) -> P.
intros.
apply typ_inversion with e (App u v) T; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with V Ur; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_pair :
   forall (P : Prop) e T u v T',
   typ e (Pair T u v) T' ->
   (forall T U V : term, forall s1 s2,
     typ e U (Srt s1) ->
     typ e u U -> typ (U :: e) V (Srt s2) -> typ e v (subst u V) ->
     T = (Sum U V) -> conv T' (Sum U V) -> P) -> P.
intros.
apply typ_inversion with e (Pair T u v) T'; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with T U V s1 s2 ; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_prod :
   forall (P : Prop) e T (U s : term),
   typ e (Prod T U) s ->
   (forall s1 s2,
    typ e T (Srt s1) -> typ (T :: e) U (Srt s2) -> conv (Srt s2) s -> P) -> P.
intros.
apply typ_inversion with e (Prod T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with s1 s2; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_sum :
   forall (P : Prop) e T (U s : term),
   typ e (Sum T U) s ->
   (forall s1 s2,
    typ e T (Srt s1) -> typ (T :: e) U (Srt s2) -> conv (Srt s2) s -> P) -> P.
intros.
apply typ_inversion with e (Sum T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with s1 s2; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_subset :
   forall (P : Prop) e T (U s : term),
   typ e (Subset T U) s ->
   (typ e T (Srt set) -> typ (T :: e) U (Srt prop) -> conv (Srt set) s -> P) -> P.
intros.
apply typ_inversion with e (Subset T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.
Qed.

Lemma inv_typ_pi1 : 
  forall (P : Prop) e t T,
   typ e (Pi1 t) T ->
   (forall U V, typ e t (Sum U V) ->  conv U T -> P) -> P.
Proof.
intros.
apply typ_inversion with e (Pi1 t) T; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with U V ; auto with coc.
Qed.

Lemma inv_typ_pi2 : 
  forall (P : Prop) e t T,
   typ e (Pi2 t) T ->
   (forall U V, typ e t (Sum U V) ->  conv (subst (Pi1 t) V) T -> P) -> P.
Proof.
intros.
apply typ_inversion with e (Pi2 t) T; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with U V ; auto with coc.
Qed.

Lemma inv_typ_let_in : 
  forall (P : Prop) e v t T,
   typ e (Let_in v t) T ->
   (forall V, typ e v V -> 
   forall s1, typ e V (Srt s1) ->
   forall T', typ (V :: e) t T' ->
   forall s2, typ (V :: e) T' (Srt s2) ->
   conv (subst v T')  T -> P) -> P.
Proof.
intros.
apply typ_inversion with e (Let_in v t) T; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply (H0 U H1 s1 H2 M H3 s2 H4) ; auto with coc.
Qed.


  Lemma typ_mem_kind : forall e t T, mem_sort kind t -> ~ typ e t T.
red in |- *; intros.
apply typ_inversion with e t T; auto with coc core arith datatypes.
generalize e T.
clear H0.
elim H; simpl in |- *; auto with coc core arith datatypes; intros.
apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

apply typ_inversion with (u :: e0) v (Srt s2);
 auto with coc core arith datatypes.

apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

apply typ_inversion with (u :: e0) v U; auto with coc core arith datatypes.

apply typ_inversion with e0 u (Prod V Ur); auto with coc core arith datatypes.

apply typ_inversion with e0 v V; auto with coc core arith datatypes.

rewrite H6 in H0.
rewrite H6 in H1.
simpl in H1.
apply H1 with e0 (Srt s2) s1 s2 ;  auto with coc core arith datatypes.
apply typ_inversion with e0 u U; auto with coc core arith datatypes.
apply typ_inversion with e0 v (subst u V); auto with coc core arith datatypes.

apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

apply typ_inversion with (u :: e0) v (Srt s2); auto with coc core arith datatypes.

apply typ_inversion with e0 u (Srt set); auto with coc core arith datatypes.

apply typ_inversion with (u :: e0) v (Srt prop); auto with coc core arith datatypes.

apply typ_inversion with e0 u (Sum U V); auto with coc core arith datatypes.

apply typ_inversion with (e0) u (Sum U V); auto with coc core arith datatypes.

apply typ_inversion with e0 u U; auto with coc core arith datatypes.

apply typ_inversion with (U :: e0) v M; auto with coc core arith datatypes.
Qed.


  Lemma inv_typ_conv_kind : forall e t T, conv t (Srt kind) -> ~ typ e t T.
intros.
apply typ_mem_kind.
apply red_sort_mem.
elim church_rosser with t (Srt kind); intros;
 auto with coc core arith datatypes.
rewrite (red_normal (Srt kind) x); auto with coc core arith datatypes.
red in |- *; red in |- *; intros.
inversion_clear H2.
Qed.



  Inductive ins_in_env A : nat -> env -> env -> Prop :=
    | ins_O : forall e, ins_in_env A 0 e (A :: e)
    | ins_S :
        forall n e f t,
        ins_in_env A n e f ->
        ins_in_env A (S n) (t :: e) (lift_rec 1 t n :: f).

  Hint Resolve ins_O ins_S: coc.

  Lemma ins_item_ge :
   forall A n e f,
   ins_in_env A n e f ->
   forall v : nat, n <= v -> forall t, item _ t e v -> item _ t f (S v).
simple induction 1; auto with coc core arith datatypes.
simple destruct v; intros.
inversion_clear H2.

inversion_clear H3; auto with coc core arith datatypes.
Qed.

  Lemma ins_item_lt :
   forall A n e f,
   ins_in_env A n e f ->
   forall v : nat,
   n > v -> forall t, item_lift t e v -> item_lift (lift_rec 1 t n) f v.
simple induction 1.
intros.
inversion_clear H0.

simple destruct v; intros.
elim H3; intros.
rewrite H4.
exists (lift_rec 1 t n0); auto with coc core arith datatypes.
inversion_clear H5.
elim permute_lift with t n0; auto with coc core arith datatypes.

elim H3; intros.
rewrite H4.
inversion_clear H5.
elim H1 with n1 (lift (S n1) x); intros; auto with coc core arith datatypes.
exists x0; auto with coc core arith datatypes.
pattern (lift (S (S n1)) x0) at 1 in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
elim H5.
change
  (lift_rec 1 (lift (S (S n1)) x) (S n0) =
   lift 1 (lift_rec 1 (lift (S n1) x) n0)) in |- *.
rewrite (permute_lift (lift (S n1) x) n0).
unfold lift at 2 in |- *.
pattern (lift (S (S n1)) x) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.
Qed.


  Lemma typ_weak_weak :
   forall A e t T,
   typ e t T ->
   forall n f,
   ins_in_env A n e f -> wf f -> typ f (lift_rec 1 t n) (lift_rec 1 T n).
simple induction 1; simpl in |- *; intros; auto with coc core arith datatypes.
elim (le_gt_dec n v); intros; apply type_var;
 auto with coc core arith datatypes.
elim H1; intros.
exists x.
rewrite H4.
unfold lift in |- *.
rewrite simpl_lift_rec; simpl in |- *; auto with coc core arith datatypes.

apply ins_item_ge with A n e0; auto with coc core arith datatypes.

apply ins_item_lt with A e0; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T0 n :: f)).
intro.
apply type_abs with s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

rewrite distr_lift_subst.
apply type_app with (lift_rec 1 V n); auto with coc core arith datatypes.

apply type_pair with s1 s2 ; auto with coc core arith datatypes.
apply H5 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

rewrite <- distr_lift_subst.
apply H7 ; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T0 n :: f)).
intro.
apply type_prod with s1; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.


cut (wf (lift_rec 1 T0 n :: f)).
intro.
apply type_sum with s1; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T0 n :: f)).
intro.
apply type_subset ; auto with coc core arith datatypes.
apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with (lift_rec 1 V (S n)) ; auto with coc.

rewrite distr_lift_subst.
simpl.
apply type_pi2 with (lift_rec 1 U n); auto with coc.

cut (wf (lift_rec 1 U n :: f)).
intro.
rewrite distr_lift_subst.
apply type_let_in with (lift_rec 1 U n) s1 s2 ; auto with coc core.
apply wf_var with s1 ; auto with coc core.

apply type_conv with (lift_rec 1 U n) s; auto with coc core arith datatypes.
Qed.


  Theorem thinning :
   forall e t T,
   typ e t T -> forall A, wf (A :: e) -> typ (A :: e) (lift 1 t) (lift 1 T).
unfold lift in |- *.
intros.
inversion_clear H0.
apply typ_weak_weak with A e; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.
Qed.


  Lemma thinning_n :
   forall n e f,
   trunc _ n e f ->
   forall t T, typ f t T -> wf e -> typ e (lift n t) (lift n T).
simple induction n.
intros.
rewrite lift0.
rewrite lift0.
replace e with f; auto with coc core arith datatypes.
inversion_clear H; auto with coc core arith datatypes.

do 8 intro.
inversion_clear H0.
intro.
rewrite simpl_lift; auto with coc core arith datatypes.
pattern (lift (S n0) T) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
inversion_clear H0.
change (typ (x :: e0) (lift 1 (lift n0 t)) (lift 1 (lift n0 T))) in |- *.
apply thinning; auto with coc core arith datatypes.
apply H with f; auto with coc core arith datatypes.
apply typ_wf with x (Srt s); auto with coc core arith datatypes.

apply wf_var with s; auto with coc core arith datatypes.
Qed.


  Lemma wf_sort_lift :
   forall n e t, wf e -> item_lift t e n -> exists s : sort, typ e t (Srt s).
simple induction n.
simple destruct e; intros.
elim H0; intros.
inversion_clear H2.

elim H0; intros.
rewrite H1.
inversion_clear H2.
inversion_clear H.
exists s.
replace (Srt s) with (lift 1 (Srt s)); auto with coc core arith datatypes.
apply thinning; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.

intros.
elim H1; intros.
rewrite H2.
generalize H0.
inversion_clear H3; intros.
rewrite simpl_lift; auto with coc core arith datatypes.
cut (wf l); intros.
elim H with l (lift (S n0) x); intros; auto with coc core arith datatypes.
inversion_clear H3.
exists x0.
change (typ (y :: l) (lift 1 (lift (S n0) x)) (lift 1 (Srt x0))) in |- *.
apply thinning; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.

inversion_clear H3.
apply typ_wf with y (Srt s); auto with coc core arith datatypes.
Qed.



  Inductive sub_in_env t T : nat -> env -> env -> Prop :=
    | sub_O : forall e, sub_in_env t T 0 (T :: e) e
    | sub_S :
        forall e f n u,
        sub_in_env t T n e f ->
        sub_in_env t T (S n) (u :: e) (subst_rec t u n :: f).

  Hint Resolve sub_O sub_S: coc.

  Lemma nth_sub_sup :
   forall t T n e f,
   sub_in_env t T n e f ->
   forall v : nat, n <= v -> forall u, item _ u e (S v) -> item _ u f v.
simple induction 1.
intros.
inversion_clear H1; auto with coc core arith datatypes.

simple destruct v; intros.
inversion_clear H2.

inversion_clear H3; auto with coc core arith datatypes.
Qed.


  Lemma nth_sub_eq : forall t T n e f, sub_in_env t T n e f -> item _ T e n.
simple induction 1; auto with coc core arith datatypes.
Qed.


  Lemma nth_sub_inf :
   forall t T n e f,
   sub_in_env t T n e f ->
   forall v : nat,
   n > v -> forall u, item_lift u e v -> item_lift (subst_rec t u n) f v.
simple induction 1.
intros.
inversion_clear H0.

simple destruct v; intros.
elim H3; intros.
rewrite H4.
inversion_clear H5.
exists (subst_rec t u n0); auto with coc core arith datatypes.
apply commut_lift_subst; auto with coc core arith datatypes.

elim H3; intros.
rewrite H4.
inversion_clear H5.
elim H1 with n1 (lift (S n1) x); intros; auto with coc core arith datatypes.
exists x0; auto with coc core arith datatypes.
rewrite simpl_lift; auto with coc core arith datatypes.
pattern (lift (S (S n1)) x0) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
elim H5.
change
  (subst_rec t (lift 1 (lift (S n1) x)) (S n0) =
   lift 1 (subst_rec t (lift (S n1) x) n0)) in |- *.
apply commut_lift_subst; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.
Qed.


  Lemma typ_sub_weak :
   forall g (d : term) t,
   typ g d t ->
   forall e u (U : term),
   typ e u U ->
   forall f n,
   sub_in_env d t n e f ->
   wf f -> trunc _ n f g -> typ f (subst_rec d u n) (subst_rec d U n).
simple induction 2; simpl in |- *; intros; auto with coc core arith datatypes.
elim (lt_eq_lt_dec n v); [ intro Hlt_eq | intro Hlt ].
elim H2.
elim Hlt_eq; clear Hlt_eq.
case v; [ intro Hlt | intros n0 Hlt ]; intros.
inversion_clear Hlt.

simpl in |- *.
rewrite H6.
rewrite simpl_subst; auto with coc core arith datatypes.
apply type_var; auto with coc core arith datatypes.
exists x; auto with coc core arith datatypes.
apply nth_sub_sup with d t n e0; auto with coc core arith datatypes.

intro Heq; intros.
rewrite H6.
elim Heq.
rewrite simpl_subst; auto with coc core arith datatypes.
replace x with t.
apply thinning_n with g; auto with coc core arith datatypes.

apply fun_item with e0 v; auto with coc core arith datatypes.
apply nth_sub_eq with d f; auto with coc core arith datatypes.
elim Heq; auto with coc core arith datatypes.

apply type_var; auto with coc core arith datatypes.
apply nth_sub_inf with t e0; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

rewrite distr_subst.
apply type_app with (subst_rec d V n); auto with coc core arith datatypes.

apply type_pair with s1 s2 ; auto with coc core arith datatypes.
apply H6 ; auto with coc.
apply wf_var with s1 ; auto with coc.
rewrite <- distr_subst ; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with (subst_rec d V (S n)) ; auto with coc.

rewrite distr_subst.
simpl.
apply type_pi2 with (subst_rec d U0 n) ; auto with coc.

cut (wf (subst_rec d U0 n :: f)).
intro ; rewrite distr_subst.
apply type_let_in with (subst_rec d U0 n) s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core arith datatypes.

apply type_conv with (subst_rec d U0 n) s; auto with coc core arith datatypes.
Qed.

  Theorem substitution :
   forall e t u (U : term),
   typ (t :: e) u U ->
   forall d : term, typ e d t -> typ e (subst d u) (subst d U).
intros.
unfold subst in |- *.
apply typ_sub_weak with e t (t :: e); auto with coc core arith datatypes.
apply typ_wf with d t; auto with coc core arith datatypes.
Qed.

Scheme typ_dep := Induction for typ Sort Prop.


Lemma type_pair_unique : forall e t T, typ e t T -> forall U V u v, t = (Pair (Sum U V) u v) ->
   conv T (Sum U V).
Proof.
intros ; induction H ; try discriminate.
injection H0 ; intros.
rewrite H6 ; rewrite H7.
apply refl_conv.
pose (IHtyp1 H0).
apply trans_conv_conv with U0; auto with coc core arith datatypes.
Qed.

Lemma type_pair_unique2 : forall e t T, typ e t T -> 
   forall T' u v, t = (Pair T' u v) -> exists U,  exists  V, T' = Sum U V /\ conv T (Sum U V).
Proof.
intros ; induction H ; try discriminate.
injection H0 ; intros.
exists U ; exists V.
split ; auto with coc.

induction (IHtyp1 H0).
induction H3.
induction H3.
exists x ; exists x0.
split ; auto with coc.
apply trans_conv_conv with U; auto with coc core arith datatypes.
Qed.


  Theorem type_case :
   forall e t T,
   typ e t T -> (exists s : sort, typ e T (Srt s)) \/ T = Srt kind.
simple induction 1; intros; auto with coc core arith datatypes.
left.
elim wf_sort_lift with v e0 t0; auto with coc core arith datatypes; intros.
exists x; auto with coc core arith datatypes.

left.
exists s2.
apply type_prod with s1; auto with coc core arith datatypes.

left.
elim H3; intros.
elim H4; intros.
apply inv_typ_prod with e0 V Ur (Srt x); auto with coc core arith datatypes;
 intros.
exists s2.
replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

discriminate H4.

left.
exists s2.
apply type_sum with s1 ; auto with coc core arith datatypes.

case s2; auto with coc core arith datatypes.
left.
exists kind.
apply type_prop.
apply typ_wf with T0 (Srt s1); auto with coc core arith datatypes.

left.
exists kind.
apply type_set.
apply typ_wf with T0 (Srt s1); auto with coc core arith datatypes.

case s2.
right ; auto.
left.
exists kind ; apply type_prop.
apply typ_wf with T0 (Srt s1); auto with coc core arith datatypes.

left; exists kind ; apply type_set.
apply typ_wf with T0 (Srt s1); auto with coc core arith datatypes.

induction H1.
induction H1.
apply inv_typ_sum with e0 U V (Srt x) ; auto with coc core arith.
intros.
left ; exists s1 ; auto with coc core arith.
discriminate H1.

induction H1.
left.
induction H1.
exists x ; auto with coc core.
replace (Srt x) with (subst (Pi1 t0) (Srt x)).
apply substitution with U ; auto with coc core.
apply inv_typ_sum with e0 U V (Srt x) ; auto with coc core arith.
intros.
rewrite <- (conv_sort _ _ H4).
assumption.
apply type_pi1 with V ; auto with coc core arith datatypes.
unfold subst ; simpl ; auto.
discriminate H1.

induction H5.
left.
induction H5.
exists x.
replace (Srt x) with (subst t0 (Srt x)).
apply substitution with U ; auto with coc core.
unfold subst ; simpl ; auto.
right.
rewrite H5.
unfold subst ; simpl ; auto.

induction H4.
left ; exists s ; auto.
left.
exists s ; auto.
Qed.

  Lemma type_free_db : forall e t T, typ e t T -> free_db (length e) T.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
inversion_clear H0.
apply typ_free_db with (Srt x); auto with coc core arith datatypes.

rewrite H0; auto with coc core arith datatypes.
Qed.

  Inductive red1_in_env : env -> env -> Prop :=
    | red1_env_hd : forall e t u, red1 t u -> red1_in_env (t :: e) (u :: e)
    | red1_env_tl :
        forall e f t, red1_in_env e f -> red1_in_env (t :: e) (t :: f).

  Hint Resolve red1_env_hd red1_env_tl: coc.

  Lemma red_item :
   forall n t e,
   item_lift t e n ->
   forall f,
   red1_in_env e f ->
   item_lift t f n \/
   (forall g, trunc _ (S n) e g -> trunc _ (S n) f g) /\
   ex2 (fun u => red1 t u) (fun u => item_lift u f n).
simple induction n.
do 3 intro.
elim H.
do 4 intro.
rewrite H0.
inversion_clear H1.
intros.
inversion_clear H1.
right.
split; intros.
inversion_clear H1; auto with coc core arith datatypes.

exists (lift 1 u).
unfold lift in |- *; auto with coc core arith datatypes.

exists u; auto with coc core arith datatypes.

left.
exists x; auto with coc core arith datatypes.

do 5 intro.
elim H0.
do 4 intro.
rewrite H1.
inversion_clear H2.
intros.
inversion_clear H2.
left.
exists x; auto with coc core arith datatypes.

elim H with (lift (S n0) x) l f0; auto with coc core arith datatypes; intros.
left.
elim H2; intros.
exists x0; auto with coc core arith datatypes.
rewrite simpl_lift.
pattern (lift (S (S n0)) x0) in |- *.
rewrite simpl_lift.
elim H5; auto with coc core arith datatypes.

right.
elim H2.
simple induction 2; intros.
split; intros.
inversion_clear H9; auto with coc core arith datatypes.

elim H8; intros.
exists (lift (S (S n0)) x1).
rewrite simpl_lift.
pattern (lift (S (S n0)) x1) in |- *.
rewrite simpl_lift.
elim H9; unfold lift at 1 3 in |- *; auto with coc core arith datatypes.

exists x1; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.
Qed.



  Lemma typ_red_env :
   forall e t T, typ e t T -> forall f, red1_in_env e f -> wf f -> typ f t T.
simple induction 1; intros.
auto with coc core arith datatypes.

auto with coc core arith datatypes.

elim red_item with v t0 e0 f; auto with coc core arith datatypes; intros.
inversion_clear H4.
inversion_clear H6.
elim H1; intros.
elim item_trunc with term v e0 x0; intros; auto with coc core arith datatypes.
elim wf_sort with v e0 x1 x0; auto with coc core arith datatypes.
intros.
apply type_conv with x x2; auto with coc core arith datatypes.
rewrite H6.
replace (Srt x2) with (lift (S v) (Srt x2));
 auto with coc core arith datatypes.
apply thinning_n with x1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

apply type_pair with s1 s2; auto with coc core arith datatypes.
apply H5 ; auto with coc.
apply wf_var with s1 ; auto with coc core.

cut (wf (T0 :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with V ; auto with coc core arith datatypes.

apply type_pi2 with U ; auto with coc core arith datatypes.

cut (wf (U :: f)); intros.
apply type_let_in with U s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.

apply type_conv with U s; auto with coc core arith datatypes.
Qed.

  Inductive red1_exp_in_env : env -> env -> Prop :=
    | red1_exp_env_hd : forall e t u, red1 t u -> red1_exp_in_env (u :: e) (t :: e)
    | red1_exp_env_tl :
        forall e f t, red1_exp_in_env e f -> red1_exp_in_env (t :: e) (t :: f).

  Hint Resolve red1_exp_env_hd red1_exp_env_tl: coc.

  Lemma exp_item :
   forall n t e,
   item_lift t e n ->
   forall f,
   red1_exp_in_env e f ->
   item_lift t f n \/
   (forall g, trunc _ (S n) e g -> trunc _ (S n) f g) /\
   ex2 (fun u => red1 u t) (fun u => item_lift u f n).
simple induction n.
do 3 intro.
elim H.
do 4 intro.
rewrite H0.
inversion_clear H1.
intros.
inversion_clear H1.
right.
split; intros.
inversion_clear H1; auto with coc core arith datatypes.

exists (lift 1 t0) ;
unfold lift in |- *; auto with coc core arith datatypes.

exists t0; auto with coc core arith datatypes.

left.
exists x; auto with coc core arith datatypes.

do 5 intro.
elim H0.
do 4 intro.
rewrite H1.
inversion_clear H2.
intros.
inversion_clear H2.
left.
exists x; auto with coc core arith datatypes.

elim H with (lift (S n0) x) l f0; auto with coc core arith datatypes; intros.
left.
elim H2; intros.
exists x0; auto with coc core arith datatypes.
rewrite simpl_lift.
pattern (lift (S (S n0)) x0) in |- *.
rewrite simpl_lift.
elim H5; auto with coc core arith datatypes.

right.
elim H2.
simple induction 2; intros.
split; intros.
inversion_clear H9; auto with coc core arith datatypes.

elim H8; intros.
exists (lift (S (S n0)) x1).
rewrite simpl_lift.
pattern (lift (S (S n0)) x) in |- *.
rewrite simpl_lift.
rewrite H9 in H7.
unfold lift.
apply red1_lift.
assumption.

exists x1; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.
Qed.

  Lemma typ_exp_env :
   forall e t T, typ e t T -> forall f, red1_exp_in_env e f -> wf f -> typ f t T.
simple induction 1; intros.
auto with coc core arith datatypes.

auto with coc core arith datatypes.

elim exp_item with v t0 e0 f; auto with coc core arith datatypes; intros.
inversion_clear H4.
inversion_clear H6.
elim H1; intros.
elim item_trunc with term v e0 x0; intros; auto with coc core arith datatypes.
elim wf_sort with v e0 x1 x0; auto with coc core arith datatypes.
intros.
apply type_conv with x x2; auto with coc core arith datatypes.
rewrite H6.
replace (Srt x2) with (lift (S v) (Srt x2));
 auto with coc core arith datatypes.
apply thinning_n with x1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

apply type_pair with s1 s2; auto with coc core arith datatypes.
apply H5 ; auto with coc.
apply wf_var with s1 ; auto with coc core.

cut (wf (T0 :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with V ; auto with coc core arith datatypes.

apply type_pi2 with U ; auto with coc core arith datatypes.

cut (wf (U :: f)); intros.
apply type_let_in with U s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.

apply type_conv with U s; auto with coc core arith datatypes.
Qed.

Inductive conv_in_env : env -> env -> Prop :=
| conv_env_hd : forall e t u, conv t u -> conv_in_env (u :: e) (t :: e)
| conv_env_tl :
        forall e f t, conv_in_env e f -> conv_in_env (t :: e) (t :: f).

  Hint Resolve conv_env_hd conv_env_tl: coc.

  Lemma conv_item :
   forall n t e,
   item_lift t e n ->
   forall f,
   conv_in_env e f ->
   item_lift t f n \/
   (forall g, trunc _ (S n) e g -> trunc _ (S n) f g) /\
   ex2 (fun u => conv t u) (fun u => item_lift u f n).
simple induction n.
do 3 intro.
elim H.
do 4 intro.
rewrite H0.
inversion_clear H1.
intros.
inversion_clear H1.
right.
split; intros.
inversion_clear H1; auto with coc core arith datatypes.

exists (lift 1 t0) ;
unfold lift in |- *; auto with coc core arith datatypes.

exists t0; auto with coc core arith datatypes.

left.
exists x; auto with coc core arith datatypes.

do 5 intro.
elim H0.
do 4 intro.
rewrite H1.
inversion_clear H2.
intros.
inversion_clear H2.
left.
exists x; auto with coc core arith datatypes.

elim H with (lift (S n0) x) l f0; auto with coc core arith datatypes; intros.
left.
elim H2; intros.
exists x0; auto with coc core arith datatypes.
rewrite simpl_lift.
pattern (lift (S (S n0)) x0) in |- *.
rewrite simpl_lift.
elim H5; auto with coc core arith datatypes.

right.
elim H2.
simple induction 2; intros.
split; intros.
inversion_clear H9; auto with coc core arith datatypes.

elim H8; intros.
exists (lift (S (S n0)) x1).
rewrite simpl_lift.
pattern (lift (S (S n0)) x1) in |- *.
rewrite simpl_lift.
unfold lift at 1 3 ; apply conv_conv_lift.
rewrite H9 in H7.
assumption.

exists x1; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.
Qed.

Lemma typ_conv_env :
forall e t T, typ e t T -> forall f, conv_in_env e f -> wf f -> typ f t T.
simple induction 1; intros.
auto with coc core arith datatypes.

auto with coc core arith datatypes.

elim conv_item with v t0 e0 f; auto with coc core arith datatypes; intros.
inversion_clear H4.
inversion_clear H6.
elim H1; intros.
elim item_trunc with term v e0 x0; intros; auto with coc core arith datatypes.
elim wf_sort with v e0 x1 x0; auto with coc core arith datatypes.
intros.
apply type_conv with x x2; auto with coc core arith datatypes.
rewrite H6.
replace (Srt x2) with (lift (S v) (Srt x2));
 auto with coc core arith datatypes.
apply thinning_n with x1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

apply type_pair with s1 s2; auto with coc core arith datatypes.
apply H5 ; auto with coc.
apply wf_var with s1 ; auto with coc core.

cut (wf (T0 :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_sum with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_subset; auto with coc core arith datatypes.

apply wf_var with set; auto with coc core arith datatypes.

apply type_pi1 with V ; auto with coc core arith datatypes.

apply type_pi2 with U ; auto with coc core arith datatypes.

cut (wf (U :: f)); intros.
apply type_let_in with U s1 s2 ; auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.

apply type_conv with U s; auto with coc core arith datatypes.
Qed.


  Lemma subj_red : forall e t T, typ e t T -> forall u, red1 t u -> typ e u T.
induction 1; intros.
inversion_clear H0.

inversion_clear H0.

inversion_clear H1.

inversion_clear H2.
cut (wf (M' :: e)); intros.
apply type_conv with (Prod M' U) s2; auto with coc core arith datatypes.
apply type_abs with s1 s2; auto with coc core arith datatypes.
apply typ_red_env with (T :: e); auto with coc core arith datatypes.

apply typ_red_env with (T :: e); auto with coc core arith datatypes.

apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

apply type_abs with s1 s2; auto with coc core arith datatypes.

elim type_case with e u (Prod V Ur); intros;
 auto with coc core arith datatypes.
inversion_clear H2.
apply inv_typ_prod with e V Ur (Srt x); intros;
 auto with coc core arith datatypes.
generalize H H0. clear H H0.
inversion_clear H1; intros.
apply inv_typ_abs with e T M (Prod V Ur); intros;
 auto with coc core arith datatypes.
apply type_conv with (subst v T0) s2; auto with coc core arith datatypes.
apply substitution with T; auto with coc core arith datatypes.
apply type_conv with V s0; auto with coc core arith datatypes.
apply inv_conv_prod_l with Ur T0; auto with coc core arith datatypes.

unfold subst in |- *.
apply conv_conv_subst; auto with coc core arith datatypes.
apply inv_conv_prod_r with T V; auto with coc core arith datatypes.

replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

apply type_conv with (subst N2 Ur) s2; auto with coc core arith datatypes.
apply type_app with V; auto with coc core arith datatypes.

unfold subst in |- *.
apply conv_conv_subst; auto with coc core arith datatypes.

replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

discriminate.

inversion_clear H3.

inversion H4.
apply type_conv with (Sum N1 V) s2 ; auto with coc.
apply type_pair with s1 s2 ; auto with coc core.
apply type_conv with U s1 ; auto with coc core.
apply typ_red_env with (U :: e); auto with coc core arith datatypes.
apply wf_var with s1 ; auto with coc core.
apply type_sum with s1 ; auto with coc.
apply type_conv with (Sum U N2) s2 ; auto with coc.
apply type_pair with s1 s2 ; auto with coc core.
apply type_conv with (subst u V) s2 ; auto with coc core.
unfold subst ; apply conv_conv_subst ; auto with coc core.
replace (Srt s2) with (subst u (Srt s2)).
apply substitution with U ; auto with coc core arith datatypes.
unfold subst ; auto.
apply type_sum with s1 ; auto with coc.

apply type_pair with s1 s2 ; auto with coc core.
apply type_conv with (subst u V) s2 ; auto with coc core.
unfold subst ; apply conv_conv_subst ; auto with coc core.
replace (Srt s2) with (subst N1 (Srt s2)).
apply substitution with U ; auto with coc core arith datatypes.
unfold subst ; auto.

apply type_pair with s1 s2 ; auto with coc core.

inversion_clear H1.
apply type_prod with s1; auto with coc core arith datatypes.
apply typ_red_env with (T :: e); auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

apply type_prod with s1; auto with coc core arith datatypes.

inversion H1.
apply type_sum with s1 ; auto with coc core.
apply typ_red_env with (T :: e)  ; auto with coc core.
apply wf_var with s1  ; auto with coc core.

apply type_sum with s1 ; auto with coc core.

inversion H1.
apply type_subset ; auto with coc core.
apply typ_red_env with (T :: e)  ; auto with coc core.
apply wf_var with set ; auto with coc core.

apply type_subset ; auto with coc core.

generalize H IHtyp ; clear H IHtyp.
inversion_clear H0 ; intros.
induction (type_case _ _ _ H).
induction H0.
apply inv_typ_sum with e U V (Srt x) ; auto ; intros.
apply inv_typ_pair with e T u N (Sum U V) ; auto with coc ; intros.
apply type_conv with U0 s1 ; auto with coc core.
pose (inv_conv_sum_l _ _ _ _ H9).
apply sym_conv ; auto.
discriminate.

pose (IHtyp _ H).
apply type_pi1 with V ; auto.

generalize H IHtyp ; clear H IHtyp.
inversion_clear H0 ; intros.

inversion_clear H.
apply type_conv with (subst M V) s2; auto with coc core.
unfold subst ; apply conv_conv_subst ; auto with coc core.
replace (Srt s2) with (subst ((Pi1 (Pair (Sum U V) M u))) (Srt s2)).
apply substitution with U ; auto with coc core arith datatypes.
apply type_pi1 with V  ; auto with coc core arith datatypes.
apply type_pair with s1 s2 ; auto with coc.
unfold subst ; simpl ; auto.

induction (type_pair_unique2 _ _ _ H0 T M u (refl_equal (Pair T M u))).
induction H.
induction H.
assert (conv (Sum U V) (Sum x x0)).
apply trans_conv_conv with U0; auto with coc.
apply type_conv with (subst M V) s ; auto with coc core.
rewrite H in H0.
apply inv_typ_pair with e (Sum x x0) M u U0 ; auto with coc core ; intros.
apply inv_typ_sum with e U V (Srt s) ; auto with coc core arith ; intros.
apply type_conv with (subst M V0) s3 ; auto with coc core.
unfold subst ; apply conv_conv_subst ; auto with coc core arith.
assert(conv (Sum U V) (Sum U1 V0)).
apply trans_conv_conv with U0 ; auto with coc core.
apply inv_conv_sum_r with U1 U ; auto with coc core.
replace (Srt s3) with (subst M (Srt s3)) ;
[ apply substitution with U ; auto with coc core | unfold subst ; simpl ; auto  ].
apply type_conv with U1 s0 ; auto with coc core.
assert(conv (Sum U V) (Sum U1 V0)).
apply trans_conv_conv with U0 ; auto with coc core.
apply inv_conv_sum_l with V0 V ; auto with coc core.

unfold subst ; apply conv_conv_subst ; auto with coc core arith.

replace (Srt s) with (subst (Pi1 (Pair T M u)) (Srt s)) ;
[ apply substitution with U | unfold subst ; simpl ; auto  ].
apply inv_typ_sum with e U V (Srt s) ; auto ; intros.
rewrite <- (conv_sort _ _ H7).
assumption.

apply type_pi1 with V.
apply type_conv with U0 s ; auto with coc core.

pose (IHtyp _ H).
induction (type_case _ _ _ t0).
induction H1.
apply type_conv with (subst (Pi1 N) V) x ; auto with coc core.
apply type_pi2 with U ; auto with coc core.
unfold subst ; apply conv_conv_subst ; auto with coc core.
apply inv_typ_sum with e U V (Srt x) ; auto ; intros.
rewrite <- (conv_sort _ _ H4).
replace (Srt s2) with (subst (Pi1 t) (Srt s2)) ;
[ apply substitution with U | unfold subst ; simpl ; auto  ].
assumption.
apply type_pi1 with V ; auto.
discriminate.

generalize H IHtyp1 H0 IHtyp2 H1 IHtyp3 H2 IHtyp4.
clear H IHtyp1 H0 IHtyp2 H1 IHtyp3 H2 IHtyp4.
inversion_clear H3 ; intros.

pose (IHtyp1 _ H).
apply type_conv with (subst N1 M) s2 ; auto with coc core.
apply type_let_in with U s1 s2 ; auto with coc core.
unfold subst ; apply conv_conv_subst ; auto with coc core arith.
replace (Srt s2) with (subst t (Srt s2)) ;
[apply substitution with U ; auto with coc core | unfold subst ; auto].

pose (IHtyp3 _ H).
apply type_let_in with U s1 s2 ; auto with coc core.

apply type_conv with U s; auto with coc core arith datatypes.
Qed.


  Theorem subject_reduction :
   forall e t u, red t u -> forall T, typ e t T -> typ e u T.
simple induction 1; intros; auto with coc core arith datatypes.
apply subj_red with P; intros; auto with coc core arith datatypes.
Qed.

  Theorem typ_unique :
   forall e t T, typ e t T -> (forall U : term, typ e t U -> conv T U).
induction 1 ; intros ; auto with coc core arith datatypes.

apply sym_conv.
apply inv_typ_prop with e; auto with coc core arith datatypes.

apply sym_conv.
apply inv_typ_set with e; auto with coc core arith datatypes.

apply inv_typ_ref with e U v; auto with coc core arith datatypes; intros.
elim H0; intros.
rewrite H4.
elim fun_item with term U0 x e v; auto with coc core arith datatypes.

apply inv_typ_abs with e T M U0; auto with coc core arith datatypes; intros.
apply trans_conv_conv with (Prod T T0); auto with coc core arith datatypes.

apply inv_typ_app with e u v U; auto with coc core arith datatypes; intros.
apply trans_conv_conv with (subst v Ur0); auto with coc core arith datatypes.
unfold subst in |- *; apply conv_conv_subst;
 auto with coc core arith datatypes.
apply inv_conv_prod_r with V V0; auto with coc core arith datatypes.

apply sym_conv.
apply type_pair_unique with e (Pair (Sum U V) u v) u v ; auto with coc core arith datatypes.

apply inv_typ_prod with e T U U0; auto with coc core arith datatypes;
 intros.
apply trans_conv_conv with (Srt s3); auto with coc core arith datatypes.

apply inv_typ_sum with e T U U0; auto with coc core arith datatypes;
 intros.
apply trans_conv_conv with (Srt s3); auto with coc core arith datatypes.

apply inv_typ_subset with e T U U0; auto with coc core arith datatypes;
 intros.

apply inv_typ_pi1 with e t U0; auto with coc core arith datatypes;
 intros.
apply trans_conv_conv with U1; auto with coc core arith datatypes.
pose (IHtyp _ H1).
apply (inv_conv_sum_l _ _ _ _ c).


apply inv_typ_pi2 with e t U0; auto with coc core arith datatypes;
 intros.
apply trans_conv_conv with (subst (Pi1 t) V0); auto with coc core arith datatypes.
unfold subst ; apply conv_conv_subst ; auto with coc core arith datatypes.
pose (IHtyp _ H1).
apply (inv_conv_sum_r _ _ _ _ c).

apply inv_typ_let_in with e t v U0; auto with coc core arith datatypes;
 intros.
apply trans_conv_conv with (subst t T'); auto with coc core arith datatypes.
unfold subst ; apply conv_conv_subst ; auto with coc core arith datatypes.
pose (IHtyp1 _ H4).


apply IHtyp3.
apply typ_conv_env with (V :: e) ; auto with coc core arith.
apply (typ_wf _ _ _ H1).

apply trans_conv_conv with U; auto with coc core arith datatypes.
Qed.


  Lemma type_kind_not_conv :
   forall e t T, typ e t T -> typ e t (Srt kind) -> T = Srt kind.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
elim H1; intros.
elim inv_typ_conv_kind with e T (Srt x); auto with coc core arith datatypes.
apply typ_unique with e t; auto with coc core arith datatypes.
Qed.

  Lemma type_reduction :
   forall e t T (U : term), red T U -> typ e t T -> typ e t U.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
inversion_clear H1.
apply type_conv with T x; auto with coc core arith datatypes.
apply subject_reduction with T; auto with coc core arith datatypes.

elim red_normal with T U; auto with coc core arith datatypes.
rewrite H1.
red in |- *; red in |- *; intros.
inversion_clear H2.
Qed.



  Lemma typ_conv_conv :
   forall e u (U : term) v (V : term),
   typ e u U -> typ e v V -> conv u v -> conv U V.
intros.
elim church_rosser with u v; auto with coc core arith datatypes; intros.
apply typ_unique with e x.
apply subject_reduction with u; auto with coc core arith datatypes.

apply subject_reduction with v; auto with coc core arith datatypes.
Qed.

End Typage.

  Hint Resolve ins_O ins_S: coc.
  Hint Resolve sub_O sub_S: coc.
  Hint Resolve red1_env_hd red1_env_tl: coc.
