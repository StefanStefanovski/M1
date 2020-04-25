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
Definition Is_true (b:bool) :=
  match b with
    | true => True
    | false => False
  end.
(* On definit le la fonction et (/\) B x B vers B; (B: boolean) *)
 Delimit Scope bool_scope with bool.

Definition negB (b1 : bool) : bool :=
  match b1 with
    | false => true
    | true => false
  end.
Definition andB (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => false
  end.

Definition orB (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => true
    | false, true => true
    | false, false => false
  end.
Definition impliqueB (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => true
    | false, false => true
  end.
Definition equivB (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.
 









