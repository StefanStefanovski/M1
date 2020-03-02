Open Scope type_scope.

Section Iso_axioms. 

Variable A B C: Set.

Axiom Com: A * B = B * A.
Axiom Ass: A*(B*C) = A*B*C.
Axiom Cur: (A*B->C) = (A->B->C).
Axiom Dis: (A->B*C) = (A->B) * (A->C).
Axiom P_unit: A*unit = A.
Axiom AR_unit: (A->unit) = unit.
Axiom AL_unit: (unit->A) = A.

End Iso_axioms.

Ltac remove_unit :=   
  repeat
    match goal with 
    | |- context[?A * unit] => rewrite P_unit 
    | |- context[?A -> unit] => rewrite AR_unit 
    | |- context[unit -> ?A] => rewrite AL_unit
    end.
Goal forall A B C: Set, (A*unit->B*(C*unit)) = 
(A*unit->(C->unit)*C)*(unit->A->B).

intros.
remove_unit.
rewrite (Dis A unit C).
rewrite 






