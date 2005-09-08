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

Inductive wfd : ctx -> Prop :=
  | WfEmpty : wfd nil
  | WfVar : forall G A s, typed G A (sort s) -> wfd (A :: G)

with typed : ctx -> term -> term -> Prop :=
  | Var : forall G, wfd G -> forall i, i < length G -> typed G (rel i) (lift i (nth i G sortS))

  | Prod : forall G A B s_1 s_2, typed G A (sort s_1) -> typed (A :: G) B (sort s_2) ->
    forall s_3, R s_1 s_2 = Some s_3 -> typed G (Pi A B) (sort s_3)
    
  | Abs : forall G A B x s, typed G (Pi A B) s -> typed (A :: G) x B ->
    typed G (lambda A x) (Pi A B)

  | SortT : forall s t, SortR s t -> typed nil (sort s) (sort t)

  | App : forall G A B f x, typed G f (Pi A B) -> typed G x A ->
    typed G (app f x) (subst x B)

  | LetIn : forall G A B x y, typed G x A -> typed (A :: G) y B ->
    typed G (let_in x y) (subst x B)

  | Sum : forall G A B s_1 s_2, typed G A (sort s_1) -> typed (A :: G) B (sort s_2) ->
    forall s_3, R s_1 s_2 = Some s_3  -> typed G (Sigma A B) (sort s_3)

  | Pair : forall G A B s x y, typed G (Sigma A B) s -> typed G x A -> typed G y (subst x B) -> 
    typed G (pair x y) (Sigma A B)

  | LetTuple : forall G A B C x y, typed G x (Sigma A B) -> typed (B :: A :: G) y C ->
    typed G (let_tuple x y) C

  | SubsetI : forall G A P, typed G A sortS -> typed (A :: G) P sortP ->
    typed G (Subset A P) sortS

  | Conv : forall G x A, typed G x A -> forall B, conv A B -> typed G x B

  | Subsum : forall G x A, typed G x A -> forall B, coerced A B -> typed G x B.


Hint Resolve WfEmpty WfVar : CCP.
Hint Resolve Var Prod Abs SortT App LetIn Sum Pair LetTuple SubsetI Conv Subsum : CCP.

Scheme typed_mut := Induction for typed Sort Prop
with wfd_mut := Induction for wfd Sort Prop.

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

Lemma weakening : forall G G' t T, typed (G' ++ G) t T -> 
  forall S, wfd (G' ++ (S :: G)) -> typed (G' ++ (S :: G)) (lift_rec 1 t (length G'))
  (lift_rec 1 T (length G')).
Proof.
  intros.
  induction H.
  
  


(* 
 Local Variables:
 coq-prog-name: "coqtop.opt -emacs -R . CCP"
 End:
*)
