Require Export Coq.Lists.List.
Require Export Coq.Arith.Compare_dec.
Require Import Coq.Relations.Relations.

Inductive Sort : Set :=
  | PropS
  | SetS
  | TypeS : nat -> Sort.

Inductive term : Set :=
  | rel : nat -> term
  | sort : Sort -> term
  | app : term -> term -> term
  | pair : term -> term -> term
  | let_tuple : term -> term -> term
  | let_in : term -> term -> term
  | lambda : term -> term -> term
  | Pi : term -> term -> term
  | Sigma : term -> term -> term
  | Subset : term -> term -> term.

Definition sortS := sort SetS.
Definition sortP := sort PropS.
Definition sortT i := sort (TypeS i).

Definition is_propset (s : Sort) := s = PropS \/ s = SetS.

Fixpoint lift_rec (n : nat) (T : term) {struct T} : nat -> term :=
  fun k : nat =>
    match T with
      | rel i => match le_gt_dec k i with
		  | left _ (* k <= i *) => rel (n + i) 
		  | right _ (* i < k *) => T
		end
      | sort s => T
      | app f t => app (lift_rec n f k) (lift_rec n t k)
      | pair x y => pair (lift_rec n x k) (lift_rec n y k)
      | let_tuple x y => let_tuple (lift_rec n x k) (lift_rec n y (S (S k)))
      | let_in x y => let_in (lift_rec n x k) (lift_rec n y (S k))
      | lambda t M => lambda (lift_rec n t k) (lift_rec n M (S k))
      | Pi A B => Pi (lift_rec n A k) (lift_rec n B (S k))
      | Sigma A B => Sigma (lift_rec n A k) (lift_rec n B (S k))
      | Subset A B => Subset (lift_rec n A k) (lift_rec n B (S k))
    end.

Definition lift (n : nat) (T : term) := lift_rec n T 0.

Fixpoint subst_rec (o T : term) {struct T} : nat -> term :=
  fun k : nat =>
  match T with
    | rel i => 
      match lt_eq_lt_dec i k with
	| inleft (left _) (* i < k *) => T
	| inleft (right _) (* i = k *) => lift k o
	| inright _ (* i > k *) => rel (pred i)
      end
    | sort s => T
    | app f t => app (subst_rec o f k) (subst_rec o t k)
    | pair x y => pair (subst_rec o x k) (subst_rec o y k)
    | let_tuple x y => let_tuple (subst_rec o x k) (subst_rec o y (S (S k)))
    | let_in x y => let_in (subst_rec o x k) (subst_rec o y (S k))
    | lambda t M => lambda (subst_rec o t k) (subst_rec o M (S k))
    | Pi A B => Pi (subst_rec o A k) (subst_rec o B (S k))
    | Sigma A B => Sigma (subst_rec o A k) (subst_rec o B (S k))
    | Subset A B => Subset (subst_rec o A k) (subst_rec o B (S k))
  end.

Definition subst (o T : term) := subst_rec o T 0.

Inductive free_db : nat -> term -> Prop :=
  | db_srt : forall n s, free_db n (sort s)
  | db_rel : forall k n, k > n -> free_db k (rel n)
  | db_lambda : forall k A M, free_db k A -> free_db (S k) M -> free_db k (lambda A M)
  | db_app : forall k u v, free_db k u -> free_db k v -> free_db k (app u v)
  | db_pi :
    forall k A B, free_db k A -> free_db (S k) B -> free_db k (Pi A B)
  | db_pair : forall k A B, free_db k A -> free_db k B -> free_db k (pair A B)
  | db_let_tuple : forall k A B, free_db k A -> free_db (S k) B -> 
  free_db k (let_tuple A B)
  | db_let_in : forall k A B, free_db k A -> free_db (S k) B -> 
  free_db k (let_in A B)
  | db_sigma :
    forall k A B, free_db k A -> free_db (S k) B -> free_db k (Sigma A B)
  | db_subset :
    forall k A B, free_db k A -> free_db (S k) B -> free_db k (Subset A B).



Fixpoint closed_rec (n : nat) (t : term) { struct t } : Prop :=
  match t with
    | rel i => i < n
    | sort s => True
    | app f t => closed_rec n f /\ closed_rec n t
    | pair x y => closed_rec n x /\ closed_rec n y
    | let_tuple x y => closed_rec n x /\ closed_rec (S (S n)) y
    | let_in x y => closed_rec n x /\ closed_rec (S n) y
    | lambda t M => closed_rec n t /\ closed_rec (S n) M
    | Pi A B => closed_rec n A /\ closed_rec (S n) B
    | Sigma A B => closed_rec n A /\ closed_rec (S n) B
    | Subset A B => closed_rec n A /\ closed_rec (S n) B
  end.

Definition closed (t : term) := closed_rec 0 t.

Hint Unfold lift subst closed : CCP.

Ltac autoc := auto with arith CCP.

Definition Type0 := TypeS 0.

Inductive SortR : Sort -> Sort -> Prop :=
  | PropR : SortR PropS Type0
  | SetR : SortR SetS Type0
  | TypR : forall i, SortR (TypeS i) (TypeS (S i)).
Require Import Max.
Definition R (x y : Sort) : option Sort :=
  match (x, y) with
    | (SetS, SetS) => Some SetS
    | (PropS, PropS) => Some PropS
    | (TypeS i, TypeS j) => Some (TypeS (max i j))
    | (SetS, PropS) => Some PropS
    | (TypeS _, PropS) => Some PropS  (* ??*)
    | _ => None
  end.

(* Beta reduction *)
Inductive red1: term -> term -> Prop :=
  | beta: forall t u v, red1 (app (lambda v t) u) (subst u t)

  | abs_red_l: forall t t', red1 t t' -> 
    forall u, red1 (lambda t u) (lambda t' u)
      
  | abs_red_r: forall t t':term, red1 t t' -> 
    forall u, red1 (lambda u t) (lambda u t')

  | app_red_l: forall t1 u1, red1 t1 u1 ->
    forall t2, red1 (app t1 t2) (app u1 t2)

  | app_red_r:forall t2 u2, red1 t2 u2 -> 
    forall t1, red1 (app t1 t2) (app t1 u2)

  | prod_red_l: forall t1 u1, red1 t1 u1 -> 
    forall t2, red1 (Pi t1 t2) (Pi u1 t2)

  | prod_red_r : forall t2 u2, red1 t2 u2 -> 
    forall t1, red1 (Pi t1 t2) (Pi t1 u2)

  | sigma_red_l : forall t1 u1, red1 t1 u1 -> 
    forall t2, red1 (Sigma t1 t2) (Sigma u1 t2)

  | sigma_red_r : forall t2 u2, red1 t2 u2 -> 
    forall t1, red1 (Sigma t1 t2) (Sigma t1 u2)

  | subset_red_l : forall t1 u1, red1 t1 u1 -> 
    forall t2, red1 (Subset t1 t2) (Subset u1 t2)

  | subset_red_r : forall t2 u2, red1 t2 u2 -> 
    forall t1, red1 (Subset t1 t2) (Subset t1 u2)

  | let_red_l : forall t1 u1, red1 t1 u1 ->
    forall t2, red1 (let_in t1 t2) (let_in u1 t2)

  | let_red_r : forall t2 u2, red1 t2 u2 ->
    forall t1, red1 (let_in t1 t2) (let_in t1 u2)

  | pair_red_l : forall t1 u1, red1 t1 u1 ->
    forall t2, red1 (pair t1 t2) (pair u1 t2)

  | pair_red_r : forall t2 u2, red1 t2 u2 ->
    forall t1, red1 (pair t1 t2) (pair t1 u2)

  | let_tuple_red_l : forall t1 u1, red1 t1 u1 ->
    forall t2, red1 (let_tuple t1 t2) (let_tuple u1 t2)

  | let_tuple_red_r : forall t2 u2, red1 t2 u2 ->
    forall t1, red1 (let_tuple t1 t2) (let_tuple t1 u2).


Inductive red (t : term) : term -> Prop :=
  | refl_red: red t t
  | trans_red: forall u v, red t u -> red1 u v -> red t v.

Inductive conv (t : term) : term -> Prop :=
  | refl_conv: conv t t
  | trans_conv_red: forall u v, conv t u -> red1 u v -> conv t v
  | trans_conv_exp: forall u v, conv t u -> red1 v u -> conv t v.

Inductive par_red1 : term -> term -> Prop :=
  | par_beta : forall t t', par_red1 t t' -> forall u u', par_red1 u u' ->
    forall v, par_red1 (app (lambda v t) u) (subst u' t')

  | sort_par_red: forall s, par_red1 (sort s) (sort s)

  | rel_par_red : forall n, par_red1 (rel n) (rel n)

  | lambda_par_red : forall t t', par_red1 t t' -> 
    forall v v', par_red1 v v' -> par_red1 (lambda v t) (lambda v' t')

  | app_par_red : forall t t', par_red1 t t' -> forall u u', par_red1 u u' ->
    par_red1 (app t u) (app t' u')

  | prod_par_red : forall t t', par_red1 t t' -> forall u u', par_red1 u u' ->
    par_red1 (Pi t u) (Pi t' u')

  | sigma_par_red : forall t t', par_red1 t t' -> forall u u', par_red1 u u' ->
    par_red1 (Sigma t u) (Sigma t' u')

  | subset_par_red : forall t t', par_red1 t t' -> forall u u', par_red1 u u' ->
    par_red1 (Subset t u) (Subset t' u')

  | let_par_red : forall t t', par_red1 t t' -> forall u u', par_red1 u u' ->
    par_red1 (let_in t u) (let_in t' u')
    
  | let_tuple_par_red : forall t t', par_red1 t t' -> forall u u', par_red1 u u' ->
    par_red1 (let_tuple t u) (let_tuple t' u')

  | pair_par_red : forall t t', par_red1 t t' -> forall u u', par_red1 u u' ->
    par_red1 (pair t u) (pair t' u').


Definition par_red := (clos_trans term par_red1).


Notation "t =Longrightarrow u" := (red t u) (at level 50).
Notation "t -longrightarrow u" := (red1 t u) (at level 50).

Hint Resolve beta abs_red_l abs_red_r app_red_l app_red_r prod_red_l prod_red_r : CCP.
Hint Resolve sigma_red_l sigma_red_r subset_red_l subset_red_r let_red_l let_red_r : CCP.
Hint Resolve let_tuple_red_l let_tuple_red_r pair_red_l pair_red_r : CCP.
Hint Resolve refl_red refl_conv : CCP.
Hint Resolve par_beta sort_par_red rel_par_red lambda_par_red app_par_red prod_par_red : CCP.
Hint Resolve sigma_par_red subset_par_red let_par_red let_tuple_par_red pair_par_red : CCP.

Hint Unfold par_red : CCP.

Definition normal : term -> Prop :=
  fun t : term => forall u, ~ (red1 t u).

(*Definition sn : term -> Prop := Acc _ (transp _ red1).*)

(* 
 Local Variables:
 coq-prog-name: "coqtop.opt -emacs -R . CCP"
 End:
*)
