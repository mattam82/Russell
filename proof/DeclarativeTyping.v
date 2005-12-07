Require Import CCP.Calculus.
Require Import CCP.LiftSubst.
Require Import CCP.Reduction.

(* Coercion judgment *)
Inductive coerced : term -> term -> Prop :=
  | SubConv : forall A B, conv A B -> coerced A B
  | SubPi : forall A B A' B', coerced A' A -> coerced B B' -> coerced (Pi A B) (Pi A' B')
  | SubSigma : forall A B A' B', coerced A A' -> coerced B B' -> coerced (Sigma A B) (Sigma A' B')
  | SubLeft : forall U U' P, coerced U U' -> coerced U (Subset U' P)
  | SubRight : forall U P U', coerced U U' -> coerced (Subset U P) U'
  | SubTrans : forall A B C, coerced A B ->  coerced B C -> coerced A C.

Hint Resolve SubConv SubPi SubSigma SubLeft SubRight SubTrans : CCP.

Definition ctx := list term.

Inductive wfd : ctx -> Prop :=
  | WfEmpty : wfd nil
  | WfVar : forall G A s, typed G A (sort s) -> wfd (A :: G)
with typed : ctx -> term -> term -> Prop :=
  | Var : forall G, wfd G -> 
    forall i, i < length G -> typed G (rel i) (lift i (nth i G sortS))
    
  | Prod : forall G A B s_1 s_2, 
    typed G A (sort s_1) -> typed (A :: G) B (sort s_2) ->
    forall s_3, R s_1 s_2 = Some s_3 -> typed G (Pi A B) (sort s_3)
    
  | Abs : forall G A B x s, 
    typed G (Pi A B) s -> typed (A :: G) x B ->
    typed G (lambda A x) (Pi A B)

  | SortT : forall s t, SortR s t -> typed nil (sort s) (sort t)

  | App : forall G A B f x, 
    typed G f (Pi A B) -> typed G x A ->
    typed G (app f x) (subst x B)

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

  | Conv : forall G x A, 
    typed G x A -> forall B, conv A B -> typed G x B

  | Subsum : forall G x A, 
    typed G x A -> forall B, coerced A B -> typed G x B.


Fixpoint lift_ctx_rec (n k : nat) (G : ctx) { struct G } : ctx :=
  match G with
  | nil => nil
  | cons t G' => lift_rec n t k :: (lift_ctx_rec n (pred k) G')
 end.

Definition lift_ctx (n : nat) (G : ctx) := lift_ctx_rec n (length G) G.

Hint Unfold lift_ctx lift_ctx_rec : CCP.

Hint Resolve WfEmpty WfVar : CCP.
Hint Resolve Var Prod Abs SortT App LetIn Sum Pair LetTuple SubsetI Conv Subsum : CCP.

Scheme typed_mut := Induction for typed Sort Prop
with wfd_mut := Induction for wfd Sort Prop.

Scheme typed_depind := Induction for typed Sort Prop.
Check typed_mut.

Lemma typed_wf : forall G t T, typed G t T -> wfd G.
Proof.
  induction 1 ; autoc.
Qed.

Lemma coercion_sym : forall T U, coerced T U -> coerced U T.
Proof.
  induction 1 ; autoc.
  apply SubTrans with B ; autoc.
Qed.

Lemma coercion_conversion : forall U T V, coerced T U -> conv U V -> coerced T V.
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

Lemma weakening : forall G t T U,  wfd (U :: G) ->  
  forall m G',
  m = length G' ->
  typed (G' ++ G) t T -> typed ((lift_ctx_rec 1 m G') ++ (U :: G)) (lift_rec 1 t m) (lift_rec 1 T m).
Proof.
  intros G t T.
  apply typed_mut with 
  (P := fun G : ctx => fun t T : term =>
  fun H : typed G t T =>
  forall U, 
  wfd (U :: G) ->
  forall m, forall G' : ctx,  m = length G' ->
  typed (G' ++ G) t T ->
  typed ((lift_ctx_rec 1 m G') ++ (U :: G)) (lift_rec 1 t m) (lift_rec 1 T m))
  (P0 := 
  (fun G : ctx => fun x : wfd G =>
  forall U,
  wfd (U :: G) ->
  forall m, forall G' : ctx, m = length G' ->
  wfd (G' ++ G) ->
  wfd ((lift_ctx_rec 1 m G') ++ (U :: G)))).
  
  intros.
  simpl.
  elim (le_gt_dec m i) ; auto ; intros.
  unfold lift ; rewrite simpl_lift_rec ; auto with arith.
  simpl.
  cut(nth i G0 sortS = nth (m + S i) (lift_ctx_rec 1 m G' ++ U :: G0) sortS).
  intros.
  rewrite H3.
  pose (v := Var) ; unfold lift in v.
  induction m.
  simpl.
  apply v ; rewrite (length_0_nil _ G' (sym_eq H1)) ; simpl ; auto with arith.
  rewrite H3.



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
