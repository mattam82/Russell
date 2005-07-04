Proof.
induction x.
destruct y ; auto with zarith.
destruct y ; auto with zarith.
case (IHx y) ; auto with zarith.
Defined.
