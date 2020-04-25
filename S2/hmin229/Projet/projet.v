Parameters A B C: Prop.
(* 1.1 ==>  **** Exemples de formules ****)

Lemma ex1: B -> A \/ B.
Proof.
intro.
right.
assumption.
Qed.

Lemma ex2: A \/ B -> B \/ A.
Proof.
(*tauto.*)
intro.
elim H.
intro.
right.
assumption.
intro.
left.
assumption.
Qed.

(* 2.1 ==> **** Définition de la notion de satisfiabilité, validité, insatisfiabilité*)
(* On definit le boolean (bool) pour les valeurs 
de variables de propositions*)

Inductive bool : Set :=
  | true : bool
  | false : bool.

(* On definit le la fonction et (/\) B x B vers B (B: bool) *)
 



Definition andB (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => false
  end.
Lemma exempleAndBool: forall a b: bool, andB a b = true -> a = true /\ b = true.
Proof.
intros.
elim H.
split.

