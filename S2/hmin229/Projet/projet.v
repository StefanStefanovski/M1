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


Check bool_rect.
(* bool_rect
     : forall P : bool -> Type, P true -> P false -> forall b : bool, P b 
*)
Check bool_ind.
(* bool_ind
     : forall P : bool -> Prop, P true -> P false -> forall b : bool, P b*)

Check bool_rec.
(* bool_rec
     : forall P : bool -> Set, P true -> P false -> forall b : bool, P b
*)

(* exemple que bool est soit true ou false*)
Lemma no_other_bool :
forall b:bool, b = true \/ b = false.
intros.
destruct b.
(* premier cas b est true*)
left. reflexivity.
(* deuxieme cas b est false*)
right. reflexivity.


Inductive False : Prop := .
Inductive True : Prop :=
| I : True.

Definition Is_true (b:bool) :=
  match b with
    | true => True
    | false => False
  end.
(* On definit les fonctions B x B vers B; (B: boolean) *)

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


Lemma exB1: forall a b:bool, andB a b = true -> a = true /\ b = true.
Proof.
intros. unfold andB.

.











