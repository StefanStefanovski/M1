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

Goal forall A B: Set, A*unit*B = B*(unit*A).

intros.
rewrite Ass.
rewrite P_unit.
rewrite P_unit.
rewrite Com.
reflexivity.

