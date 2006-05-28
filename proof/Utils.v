Require Import Coq.Arith.Wf_nat.

Set Implicit Arguments.
Lemma wf_lt_induction_type : forall (P : nat -> Type),
  (forall x : nat, (forall y : nat, y < x -> P y) -> P x) ->
       forall a : nat, P a.
Proof.
apply (well_founded_induction_type).
apply lt_wf.
Qed.

Inductive ex2 (A B : Type) (P : A -> B -> Prop) : Prop :=
 | ex2_intros : forall (a : A) (b : B), P a b -> ex2 (A:=A) (B:=B) P.

Notation "'exists2' x y , p" := (ex2 (fun x => fun y => p))
   (at level 200, x ident, y ident) : type_scope.

Inductive ex3 (A B C : Type) (P : A -> B -> C -> Prop) : Prop :=
 | ex3_intros : forall (a : A) (b : B) (c : C), P a b c -> ex3 (A:=A) (B:=B) (C:=C) P.

Notation "'exists3' x y w , p" := (ex3 (fun x => fun y => fun w => p))
   (at level 200, x ident, y ident, w ident) : type_scope.

Inductive ex4 (A B C D : Type) (P : A -> B -> C -> D -> Prop) : Prop :=
 | ex4_intros : forall (a : A) (b : B) (c : C) (d : D), P a b c d -> ex4 (A:=A) (B:=B) (C:=C) (D := D) P.

Notation "'exists4' w x y z , p" := (ex4 (fun w => fun x => fun y => fun z => p))
   (at level 200, w ident, x ident, y ident, z ident) : type_scope.

