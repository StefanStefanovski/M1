Parameter A: Prop.
Goal A->False->~A.
intros.
elimtype False + apply(H0).
assumption.

