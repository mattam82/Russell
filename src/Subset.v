Inductive subset (A : Type) (P : A -> Prop) : Type :=
  | elt : forall x : A, P x -> subset A P.

Check (subset nat (eq 0)).

Check (elt _ _ 0 (refl_equal 0) : subset nat (eq 0)).

Inductive atom : Set := 
  | aint | anat | abool.

Parameter var : Set.
Require Import Coq.Lists.List.
Definition vars := list var.

Fixpoint sup (x y : nat) { struct x } : bool :=
  match x with
    | 0 => true
    | S n => 
      match y with
	| 0 => false
	| S m => sup n m
      end
  end.

Definition max (x y : nat) : nat := 
  if sup x y then y else x.

Inductive type : nat -> Type :=
  | tatom : atom -> type 0
  | tsubset : forall n : nat, type n -> (nat -> Prop) -> type n
  | tdep : forall n : nat, type (S n) -> type n
  | tarrow : forall n m : nat, type n -> type m -> type (max n m)
  | tvar : forall n : nat, type n.

Inductive sigT (A : Set) (P : A -> Type) : Type :=
  existT : forall x : A, P x -> sigT A P.

Fixpoint max_supertype (n : nat) (t : type n) { struct t } : sigT nat type :=
  match t with
    | tsubset n' A P => max_supertype n' A
    | tarrow n m x y => 
      match max_supertype m y with
	existT m' ty => existT _ _ (max n m') (tarrow n m' x ty)
      end
    | _ => existT _ _ n t
  end.

Eval compute in (max_supertype 0 (tarrow 0 0 (tatom aint) (tsubset 0 (tatom aint) (fun v => True)))).

Fixpoint direct_supertype (n : nat) (t : type n) { struct t } : sigT nat type :=
  match t with
    | tsubset n' A P => direct_supertype n' A
    | _ => existT _ _ n t
  end.

Fixpoint subtype_constraints (n : nat) (t : type n) { struct t } : 
  (t : max_supertype n t) -> Prop :=
  match t with 
    | _ => (fun _ => True)
  end.