Section Ensembles.
  Variable U : Type.

  Definition Ensemble := U -> Prop.

  Definition In (V:Ensemble) (A:U) : Prop := V A.

  Definition Included (V F:Ensemble) : Prop := forall A:U, In V A -> In F A.

  Inductive Empty_set : Ensemble :=.
