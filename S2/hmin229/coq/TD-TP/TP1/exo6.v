Parameter a b c: Prop.
Goal (a\/b)->(a->c)->(b->c)->c.
intros.
elim (H).
apply H0.
apply H1.

