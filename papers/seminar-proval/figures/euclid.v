Require Import Coq.subtac.Utils.
Require Import Wf_nat.
Require Import Arith.
Require Import Omega.
Delimit Scope program_scope with program.

Print right.

Notation "'left'" := (left _ _) : program_scope.
Notation "'right'" := (right _ _) : program_scope.
Open Scope program_scope.

Program Definition lt_ge_dec (x y : nat) : { x < y } + { x >= y} :=
  if le_lt_dec y x then right else left.

Extraction Inline lt_ge_dec.
Notation " x < y " := (lt_ge_dec x y) : program_scope.

Program Fixpoint div (a : nat) (b : nat | b <> 0) { wf lt } :
  { qr : nat * nat | let (q, r) := qr in a = b * q + r } :=
  if a < b then (O, a)
  else dest div (a - b) b as (q', r) in (S q', r).

Solve Obligations using subtac_simpl ; auto ; omega.

Next Obligation.
Proof.
  intros.
  destruct_call div ; subtac_simpl.
  assert(x * S q' = (x * q') + x) by
    auto with arith.
  omega.
Qed.

Extraction div.
