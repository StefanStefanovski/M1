Parameter A B: Prop.
Goal (A<->B)->B->A.
intros.
elim H.
intros.
apply H2.
assumption.