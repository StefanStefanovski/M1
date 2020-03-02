Require Export List.
Open Scope list_scope.
Import ListNotations.

Lemma exo3: forall (E: Type) (l: list E) (e: E),
  rev(l ++ [e]) = e :: rev l.

intros.
elim l.
reflexivity.
intros.
simpl.
rewrite H.
reflexivity.
Qed.

Lemma exo4: forall (E: Type) (l: list E), rev(rev(l)) = l.

intros.
elim l.
simpl.
reflexivity.
intros.
simpl.
rewrite exo3.
rewrite H.
reflexivity.


  
