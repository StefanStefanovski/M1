Parameter A B C: Prop.
Goal (A->B->C)->(A->B)->A->C.
intros.
apply H.
assumption.
apply H0.
assumption.