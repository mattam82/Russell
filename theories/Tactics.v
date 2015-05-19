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

Ltac induction_with_subterm c H :=
  (set(x := c) ; assert(y:x = c) by reflexivity ;
  rewrite <- y in H ; 
  induction H ; subst).

Ltac induction_with_subterms c c' H :=
  let x := fresh "x" in
  let y := fresh "y" in
  let z := fresh "z" in
  let w := fresh "w" in
  (set(x := c) ; assert(y:x = c) by reflexivity ;
  set(z := c') ; assert(w:z = c') by reflexivity ;
  rewrite <- y in H ; rewrite <- w in H ; 
  induction H ; subst).


