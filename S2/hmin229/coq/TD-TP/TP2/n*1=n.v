Open Scope nat_scope.

Variables N: Set.


Goal forall n: nat, n*1 = n.

intros.
elim n.
reflexivity.
intros.
simpl.
rewrite H.
reflexivity.



