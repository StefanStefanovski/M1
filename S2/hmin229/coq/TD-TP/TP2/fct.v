Open Scope nat_scope.

Variables N: Set.

Fixpoint f(n: nat) : nat := 
  match n with 
  | 0 => 1
  | (S p) => 2 * (f p)
  end.

Goal f(10) = 1024.

simpl.
reflexivity.
