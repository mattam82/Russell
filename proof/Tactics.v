Require Import Lambda.Utils.

Ltac destruct_one_pair :=
 match goal with
 | [H : (ex _) |- _] => destruct H
 | [H : (ex2 _) |- _] => destruct H
 | [H : (ex3 _) |- _] => destruct H
 | [H : (ex4 _) |- _] => destruct H
 | [H : (_ /\ _) |- _] => destruct H
end.

Ltac destruct_exists := repeat (destruct_one_pair) .

