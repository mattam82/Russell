Require Import CCP.Calculus.
Require Import CCP.LiftSubst.
Require Import CCP.Reduction.
Require Import CCP.MyList.

Definition env := list term.

Implicit Type t T u U v V: term.
Implicit Types i k m n p : nat.
Implicit Types A B M N : term.
Implicit Types e f g : env.
Implicit Type G D : env.

Definition item_lift t e n :=
ex2 (fun u => t = lift (S n) u) (fun u => item term u (e:list term) n).

Section Typing.

(* Coercion judgment *)
Inductive coerced : term -> term -> Prop :=
  | SubConv : forall A B, conv A B -> coerced A B
  | SubPi : forall A B A' B', coerced A' A -> coerced B B' -> coerced (Pi A B) (Pi A' B')
  | SubSigma : forall A B A' B', coerced A A' -> coerced B B' -> coerced (Sigma A B) (Sigma A' B')
  | SubLeft : forall U U' P, coerced U U' -> coerced U (Subset U' P)
  | SubRight : forall U P U', coerced U U' -> coerced (Subset U P) U'
  | SubTrans : forall A B C, coerced A B ->  coerced B C -> coerced A C.

Hint Resolve SubConv SubPi SubSigma SubLeft SubRight SubTrans : CCP.


Inductive wfd : env -> Prop :=
  | WfEmpty : wfd nil
  | WfVar : forall G A s, typed G A (sort s) -> wfd (A :: G)
with typed : env -> term -> term -> Prop :=
  | Var : forall G, wfd G -> 
    forall i, i < length G -> typed G (rel i) (lift i (nth i G sortS))
    
  | Prod : forall G A B s_1 s_2, 
    typed G A (sort s_1) -> typed (A :: G) B (sort s_2) ->
    forall s_3, R s_1 s_2 = Some s_3 -> typed G (Pi A B) (sort s_3)
    
  | Abs : forall G A B x s, 
    typed G (Pi A B) s -> typed (A :: G) x B ->
    typed G (lambda A x) (Pi A B)

  | SortT : forall G, wfd G ->
    forall s s', SortR s s' -> typed G (sort s) (sort s')

  | App : forall G A B u v, 
    typed G u (Pi A B) -> typed G v A ->
    typed G (app u v) (subst v B)

  | LetIn : forall G A B x y, typed G x A -> typed (A :: G) y B ->
    typed G (let_in x y) (subst x B)

  | Sum : forall G A B s_1 s_2, 
    typed G A (sort s_1) -> typed (A :: G) B (sort s_2) ->
    forall s_3, R s_1 s_2 = Some s_3  -> typed G (Sigma A B) (sort s_3)

  | Pair : forall G A B s x y, 
    typed G (Sigma A B) s -> typed G x A -> typed G y (subst x B) -> 
    typed G (pair x y) (Sigma A B)

  | LetTuple : forall G A B C x y,
    typed G x (Sigma A B) -> typed (B :: A :: G) y C ->
    typed G (let_tuple x y) C

  | SubsetI : forall G A P, 
    typed G A sortS -> typed (A :: G) P sortP ->
    typed G (Subset A P) sortS

  | Subsum : forall G x A, 
    typed G x A -> forall B, coerced A B -> typed G x B.

Notation "G |- t : T" := (typed G t T) (at level 50).
Notation "T >> U" := (coerced T U) (at level 50).
Notation "|-  G" := (wfd G) (at level 50).


Lemma type_prop_set :
   forall s, is_propset s -> forall e, wfd e -> typed e (sort s) (sortT 0).
unfold sortT ; simple destruct 1; intros; rewrite H0.
apply SortT; trivial.
constructor.
apply SortT; trivial.
constructor.
Qed.

Lemma typ_free_db : forall e t T, typed e t T -> free_db (length e) t.
simple induction 1; intros; auto with CCP core arith datatypes.
inversion_clear H1.
apply db_rel.
elim H3; simpl in |- *; intros; auto with coc core arith datatypes.
Qed.


  Lemma typ_wf : forall e t T, typ e t T -> wf e.
simple induction 1; auto with coc core arith datatypes.
Qed.









Fixpoint lift_ctx_rec (n k : nat) (G : ctx) { struct G } : ctx :=
  match G with
  | nil => nil
  | cons t G' => lift_rec n t k :: (lift_ctx_rec n (pred k) G')
 end.

Definition lift_ctx (n : nat) (G : ctx) := lift_ctx_rec n (length G) G.

Fixpoint subst_ctx_rec (t : term) (k : nat) (G : ctx) { struct k } : ctx := 
  match k with
  | 0 => G
  | S k' =>
    match G with
    | nil => nil
    | cons u G' => subst_rec t u k' :: (subst_ctx_rec t k' G')
    end
  end.

Definition subst_ctx (t : term) (G : ctx) := subst_ctx_rec t (length G) G.

Hint Unfold lift_ctx lift_ctx_rec : CCP.

Hint Resolve WfEmpty WfVar : CCP.
Hint Resolve Var Prod Abs SortT App LetIn Sum Pair LetTuple SubsetI Subsum : CCP.

Scheme typed_mut := Induction for typed Sort Prop
with wfd_mut := Induction for wfd Sort Prop.

Scheme typed_depind := Induction for typed Sort Prop.

Lemma typed_wf : forall G t T, typed G t T -> wfd G.
Proof.
  induction 1 ; autoc.
Qed.

Lemma coercion_sym : forall T U, T >> U -> U >> T.
Proof.
  induction 1 ; autoc.
  apply SubTrans with B ; autoc.
Qed.

Lemma coercion_conversion : forall U T V, T >> U -> conv U V -> T >> V.
Proof.
  intros.
  apply SubTrans with U ; autoc.
Qed.

Hint Resolve typed_wf coercion_sym coercion_conversion : CCP.

Ltac eautoc := eauto with arith CCP.

Require Import Lt.

Set Implicit Arguments.

Lemma leq_exists : forall m i, m <= i -> exists i', i = m + i'.
Proof.
  intros m i H ; induction H.
  exists 0 ; auto with arith.
   induction IHle.
   exists (S x).
   omega.
Qed.

Lemma map_length : forall A B : Set, forall f : A -> B, forall l,
  length (map f l) = length l.
Proof.
  intros.
  induction l ; simpl ; auto.
Qed.

Lemma lift_ctx_rec_length : forall l i k, length (lift_ctx_rec i k l)  = length l.
Proof.
 induction l ; simpl ; auto.
Qed. 

Require Import CCP.ListProps.
Require Import Arith.

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




Lemma substitution : forall G A a, typed G a A ->
  forall G' t T, typed G' t T ->
  forall D, G' = D ++ A :: G -> let n := length D in  
  typed (subst_ctx_rec a n (D ++ G)) 
    (subst_rec a t n) (subst_rec a T n).
Proof.
  intros G A a Ha.
  intros G' t T Ht.
  induction Ht using typed_mut with 
  (P := fun G' : ctx => fun t T : term => fun H : typed G' t T =>
  forall D, G' = D ++ A :: G -> let n := length D in  
  typed (subst_ctx_rec a n (D ++ G))
    (subst_rec (lift (S n) a) t n) (subst_rec (lift (S n) a) T n)) 
  (P0 := fun G' : ctx => fun H : wfd G' =>
  forall D, G' = D ++ A :: G -> let n := length D in  
  wfd (subst_ctx_rec a n (D ++ G))).
  intros.
  
  induction D.
  simpl in n.
  unfold n.
  case i.
  simpl.
  rewrite lift_0.
  rewrite lift_0.
  rewrite H.
  simpl.
  
  unfold lift.  
  
rewrite simpl_subst_rec.

  simpl.
  elim (lt_eq_lt_dec i 0) ; intros.
  induction a0.
  elim (lt_n_O _ a0).
  rewrite b.
  rewrite lift_0.
  rewrite lift_0.
  rewrite H.
  simpl.
  unfold lift ; rewrite simpl_subst_rec ; auto with arith.
  rewrite lift_rec_0.
  apply Ha.
  unfold lift ; rewrite simpl_subst_rec ; auto with arith.
  rewrite simpl_lift_rec ; simpl ; auto with arith.
  rewrite H.
  simpl.
  elim i.

  simpl.

  simpl in H.
  rewrite H in w.
  inversion w.

  simpl in n.


  unfold n ; simpl.
  
  Focus 2.
  

  rewrite subst_rec_0.


  induction Ht using typed_mut with 
  (P := fun G : ctx => fun t T : term => fun H : typed G t T =>
  typed (subst_ctx_rec a n G) 
    (subst_rec a t n) (subst_rec a T n)).

  (P0 := 
  (fun G : ctx => fun x : wfd G =>
  forall U,
  wfd (U :: G) ->
  forall m, forall G' : ctx, m = length G' ->
  wfd (G' ++ G) ->
  wfd ((lift_ctx_rec 1 m G') ++ (U :: G)))).

) (Q :=   /\ (wfd (D ++ A :: G) -> wfd (subst_ctx a D ++ G)))

  induction D.

  simpl.
  elim (lt_eq_lt_dec i 0) ; intros.
  induction a0.
  elim (lt_n_O i a0).
  rewrite b.
  rewrite lift_0.
  rewrite lift_0.
  

  unfold lift ; simpl.

  induction i.


Lemma subject_reduction : forall G t t' T, (typed G t T) -> red t t' -> 
  (typed G t' T).
Proof.
  intros.
  induction H0.
  assumption.
  induction H1.
  inversion IHred.
  inversion H4.
  

Lemma unicity_sorting : forall G T s s', 
  (typed G T (sort s) /\ typed G T (sort s')) -> s = s'.
Proof.
  induction T.
  intros.
  induction H.
  inversion H ; inversion H0.
  rewrite H2 in H7.
  injection H7 ; auto.
  
  

Lemma weakening : forall G t T U,
  (|- (U :: G)) ->  
  forall m G',
  m = length G' ->
  typed (G' ++ G) (lift m t) (lift m T) -> 
  typed ((lift_ctx_rec 1 m G') ++ (U :: G)) 
         (lift (S m) t) (lift (S m) T).
Proof.
  intros G t T.
  apply typed_mut with 
  (P := fun G : ctx => fun t T : term =>
  fun H : typed G t T =>
  forall U, 
  wfd (U :: G) ->
  forall m, forall G' : ctx,  m = length G' ->
  typed (G' ++ G) (lift m t) (lift m T) ->
  typed ((lift_ctx_rec 1 m G') ++ (U :: G)) 
    (lift (S m) t) (lift (S m) T))
  (P0 := 
  (fun G : ctx => fun x : wfd G =>
  forall U,
  wfd (U :: G) ->
  forall m, forall G' : ctx, m = length G' ->
  wfd (G' ++ G) ->
  wfd ((lift_ctx_rec 1 m G') ++ (U :: G)))).
  
  intros.
  set (G'' := lift_ctx_rec 1 m G'). 
  simpl.
  cut(nth i G0 sortS = nth (S m + i) (G'' ++ U :: G0) sortS).
  intros.
  rewrite H3.
  simpl.
  pose (v := Var) ; unfold lift in v.
  unfold lift ; rewrite simpl_lift_rec ; auto with arith.
  elim (le_gt_dec m i) ; intros Hmi ; simpl.
  apply v.
  unfold G'' ; apply H ; auto.
  apply (typed_wf _ _ _ H2).
  rewrite length_app.
  unfold G'' ; rewrite lift_ctx_rec_length.
  rewrite <- H1.
  simpl.
  omega.
  apply v.
  unfold G'' ; apply H ; auto.
  apply (typed_wf _ _ _ H2).
  rewrite length_app.
  unfold G'' ; rewrite lift_ctx_rec_length.
  rewrite <- H1.
  simpl.
  omega.
  cut(S m = length (G'' ++ U :: nil)).
  intros. 
  rewrite H3.
  assert(G'' ++ U :: G0 = (G'' ++ U :: nil) ++ G0).
  rewrite <- ass_app ; auto.
  rewrite H4.
  apply nth_i_app.
  rewrite length_app.
  simpl.
  unfold G'' ; rewrite lift_ctx_rec_length ; rewrite H1; rewrite plus_comm ; auto with arith.

  (* Pi *)
  intros.
  unfold lift ; simpl ; unfold lift in H, H0 ; simpl in H, H0.
  eapply Prod.
  apply H ; auto.
  inversion H3.

  apply 
  
  unfold lift ; simpl.
  rewrite simpl_lift_rec ; auto with arith.
  

  induction G'.
  simpl.
  simpl in H1 ; rewrite H1.
  auto.




  inversion H2 ;auto.

  elim (le_gt_dec m i) ; intros.
  pose (H U H0 m G' H1 (typed_wf _ _ _ H2)).
  pose (Var _ w0 (S i)).
  assert(i >= length (lift_ctx_rec 1 m G')) ; try omega.
  unfold lift_ctx ; rewrite lift_ctx_rec_length.
  omega.
  rewrite (nth_app_middle _ U sortS (lift_ctx_rec 1 m G') G0 i H8) in t0. 
  unfold lift ; rewrite simpl_lift_rec.
  simpl.
  
  assert(lift_ctx_rec 1 m G' ++ G0 = G0).
  induction G'.
  simpl.
  auto.
  simpl.
  




  assert(
  induction G'.
  simpl.
  symmetry.
  apply extensionality.
  
  simpl nth at 1.
  


  
  unfold lift.
  rewrite H1 ; simpl.
  unfold lift in H4.
  rewrite H4.
  rewrite simpl_lift_rec ; auto with arith ; simpl.
  rewrite (nth_cons term i G0 sortS U).
  elim (le_gt_dec (length G') i)  ; intros.
  pose (v :=  Var) ; unfold lift in v ; apply v ; simpl ; auto with arith.

  elim (le_gt_dec m i).
  intros.
  



  pose (Var _ w0 (S i)).

  induction (leq_exists a).
  rewrite H3.

  pose (Var _ _  (S i)).
  

  induction a.
  simpl vapp ; simpl plus.
  pose Var.
  unfold lift in t0 ; apply t0 ; auto with arith.

  simpl vapp.

simpl.


  simpl.
  rewrite (
  rewrite (nth_app term i n0 (lt_n_S _ _ p) G0 m (lift_ctx 1 m G') U H2).

  
  induction a.
  assert(m + S i < m + S n0) ; try omega.
  pose Var.
  assert(exists i', S i = m + i').
  induction i.
  exists 1 ; omega.


   
  unfold lift in t0.
  induction m.
  apply t0.
  eapply H ; auto.
  simpl.
  apply H1.
  simpl.
  rewrite (eq_vnil _ G').
  simpl.
  assumption.

  simpl.
  

apply w.
  apply (t0 (m + S n0).


inversion G0.

  induction m ; simpl ; intros G G' U t T Ht Hw. 
  rewrite (eq_vnil _ G').
  rewrite (eq_vnil _ G') in Ht.
  rewrite (eq_vnil _ G') in Hw.
  simpl in Ht, Hw.
  simpl.
  induction Ht using typed_depind.

  simpl.
  unfold lift.
  rewrite simpl_lift_rec ; auto with arith.
  simpl.
  rewrite (cons_nth term n i G U).
  pose Var.
  unfold lift in t.
  apply t ; auto.
  
  simpl ; simpl in IHHt1, IHHt2.
  eapply Prod.
  apply IHHt1; auto.
  
  

  Lemma ctx_permut : forall n, forall U A, forall G : ctx n,
  wfd (S n) (U ::: G) -> wfd (S n) (A ::: G) ->
  


  apply Var.

  induction 1 using typed_mut with (P0 := fun n : nat => fun G0 : ctx n => fun w : wfd n G0 =>
    wfd (S n) (U ::: G0)).

  intros.
  simpl.
  elim (le_gt_dec m i) ; intros.
  unfold lift.
  rewrite simpl_lift_rec ; autoc.
  simpl.

  Check Var.
  unfold vapp ; simpl.

  eapply Var.

  rewrite IHHt.
  cut(nth i (lift_ctx 1 G' ++ G) sortS = nth (S i) (lift_ctx 1 G' ++ (U :: G)) sortS).
  intros H ; rewrite H.
  simpl.
  pose Var.
  unfold lift in t.
  apply t ; autoc.
  


  Check Var.

  simpl.
  
  
  
  


(* 
 Local Variables:
 coq-prog-name: "coqtop.opt -emacs -R . CCP"
 End:
*)
