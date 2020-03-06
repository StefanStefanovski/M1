(* $Id$ *)

Section puzzle.

Parameters Scottish RedSocks WearKilt Married GoOutSunday : Prop.

Hypothesis rule1 : ~ Scottish -> RedSocks.
Hypothesis rule2 : WearKilt \/ ~ RedSocks.
Hypothesis rule3 : Married -> ~ GoOutSunday.
Hypothesis rule4 : GoOutSunday <-> Scottish.
Hypothesis rule5 : WearKilt -> Scottish /\ Married.
Hypothesis rule6 : Scottish -> WearKilt.

Lemma NoMember : False.
Proof.
  apply rule3.
  apply rule5.
  elim rule2.
  intro.
  assumption.
  intro.
  elim H.
  apply rule1.
  intro.
  apply rule3.
  apply rule5.
  apply rule6.
  assumption.
  elim rule4.
  intros.
  apply H2.
  assumption.
  elim rule4.
  intros.
  apply H0.
  apply rule5.
  elim rule2.
  intros.
  assumption.
  intro.
  elim H1.
  apply rule1.
  intro.
  apply rule3.
  apply rule5.
  apply rule6.
  assumption.
  elim rule4.
  intros.
  apply H4.
  assumption.
Qed.

End puzzle.
