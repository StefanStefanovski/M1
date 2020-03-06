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
  apply rule6.
  elim H.
  apply rule1.
  intro.
  apply rule3.
  apply rule5.
  apply rule6.
  assumption.
  apply rule4.
  assumption.
  apply rule4.
  elim rule2.
  intro.
  apply rule5.
  assumption.
  intro.
  elim H.
  apply rule1.
  intro.
  apply rule3.
  apply rule5.
  apply rule6.
  assumption.
  apply rule4.
  assumption.
Qed.

End puzzle.
