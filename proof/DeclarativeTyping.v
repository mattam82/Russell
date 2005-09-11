Require Import CCP.Calculus.
Require Import CCP.LiftSubst.
Require Import CCP.Reduction.

Require Import CCP.Vector.

(* Coercion judgment *)
Inductive coerced : term -> term -> Prop :=
  | SubConv : forall A B, conv A B -> coerced A B
  | SubPi : forall A B A' B', coerced A' A -> coerced B B' -> coerced (Pi A B) (Pi A' B')
  | SubSigma : forall A B A' B', coerced A A' -> coerced B B' -> coerced (Sigma A B) (Sigma A' B')
  | SubLeft : forall U U' P, coerced U U' -> coerced U (Subset U' P)
  | SubRight : forall U P U', coerced U U' -> coerced (Subset U P) U'
  | SubTrans : forall A B C, coerced A B ->  coerced B C -> coerced A C.

Hint Resolve SubConv SubPi SubSigma SubLeft SubRight SubTrans : CCP.


Definition ctx (n : nat) := @vec term n.

Infix ":::" := vcons (at level 60, right associativity) : vec_scope.

Open Scope vec_scope.

Check (vcons).
Check nth.
Inductive wfd : forall n : nat, ctx n -> Prop :=
  | WfEmpty : wfd 0 vnil 
  | WfVar : forall n, forall G : ctx n, forall A s, typed n G A (sort s) -> wfd (S n) (A ::: G)
with typed : forall n : nat, ctx n -> term -> term -> Prop :=
  | Var : forall n, forall G : ctx n, wfd n G -> 
    forall i, forall p : i < n, typed n G (rel i) (lift i (nth i n p G))
    
  | Prod : forall n, forall G : ctx n, forall A B s_1 s_2, 
    typed n G A (sort s_1) -> typed (S n) (A ::: G) B (sort s_2) ->
    forall s_3, R s_1 s_2 = Some s_3 -> typed n G (Pi A B) (sort s_3)
    
  | Abs : forall n, forall G : ctx n, forall A B x s, 
    typed n G (Pi A B) s -> typed (S n) (A ::: G) x B ->
    typed n G (lambda A x) (Pi A B)

  | SortT : forall s t, SortR s t -> typed 0 vnil (sort s) (sort t)

  | App : forall n, forall G : ctx n, forall A B f x, 
    typed n G f (Pi A B) -> typed n G x A ->
    typed n G (app f x) (subst x B)

  | LetIn : forall n, forall G : ctx n, forall A B x y, typed n G x A -> typed (S n) (A ::: G) y B ->
    typed n G (let_in x y) (subst x B)

  | Sum : forall n, forall G : ctx n, forall A B s_1 s_2, 
    typed n G A (sort s_1) -> typed (S n) (A ::: G) B (sort s_2) ->
    forall s_3, R s_1 s_2 = Some s_3  -> typed n G (Sigma A B) (sort s_3)

  | Pair : forall n, forall G : ctx n, forall A B s x y, 
    typed n G (Sigma A B) s -> typed n G x A -> typed n G y (subst x B) -> 
    typed n G (pair x y) (Sigma A B)

  | LetTuple : forall n, forall G : ctx n, forall A B C x y,
    typed n G x (Sigma A B) -> typed (S (S n)) (B ::: A ::: G) y C ->
    typed n G (let_tuple x y) C

  | SubsetI : forall n, forall G : ctx n, forall A P, 
    typed n G A sortS -> typed (S n) (A ::: G) P sortP ->
    typed n G (Subset A P) sortS

  | Conv : forall n, forall G : ctx n, forall x A, 
    typed n G x A -> forall B, conv A B -> typed n G x B

  | Subsum : forall n, forall G : ctx n, forall x A, 
    typed n G x A -> forall B, coerced A B -> typed n G x B.


Definition lift_ctx_rec (n k l : nat) (G : ctx l) :=
  vmap l term term (fun t => lift_rec n t k) G.

Definition lift_ctx (n l : nat) (G : ctx l) := lift_ctx_rec n 0 l G.

Hint Unfold lift_ctx lift_ctx_rec : CCP.

Hint Resolve WfEmpty WfVar : CCP.
Hint Resolve Var Prod Abs SortT App LetIn Sum Pair LetTuple SubsetI Conv Subsum : CCP.

Scheme typed_mut := Induction for typed Sort Prop
with wfd_mut := Induction for wfd Sort Prop.

Scheme typed_depind := Induction for typed Sort Prop.

Lemma typed_wf : forall n, forall G : ctx n, forall t T, typed n G t T -> wfd n G.
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
Infix "+++" := vapp (right associativity, at level 60) : vector_scope.

Lemma weakening : forall n m, forall G : ctx n, forall G' : ctx m, forall t T, 
  typed (m + n) (vapp term m n G' G) t T ->
  forall U,
  wfd (m + S n) (vapp term m (S n) (lift_ctx 1 m G') (U ::: G)) -> 
  typed (m + S n) (vapp term m (S n) (lift_ctx 1 m G') (U ::: G)) (lift_rec 1 t m)
  (lift_rec 1 T m).
Proof.
  intros n m.
  intros G G' t T Ht.
  induction Ht ; simpl ; intros.

  elim (le_gt_dec m i) ; intros.
  unfold lift.
  rewrite simpl_lift_rec ; auto with arith.
  simpl.
  rewrite (cons_nth term n0 i G0 U).
  pose Var.
  unfold lift in t.


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
