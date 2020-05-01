Variables A B C: Prop.
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
(*preuves d'associativité a gauche*)
Lemma AssocEt: forall (A B C :Prop), (A /\ B /\ C) -> 
              ((A /\ B) /\ C).
Proof.
  intros.
  elim H.
  intros.
  elim H1.
  intros.
  split.
  split.
  assumption. assumption. assumption.
Qed.
Lemma AssocOu: forall (A B C : Prop),(A \/ B \/ C) ->
               ((A \/ B) \/ C).
Proof.
  intros.
  elim H.
  intros.
  left.
  left.
  assumption.
  intros.
  elim H0.
  intros.
  left; right; assumption.
  intros.
  right; assumption.
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
Proof.
intros.
destruct b.
(* premier cas b est true*)
left. reflexivity.
(* deuxieme cas b est false*)
right. reflexivity.
Qed. 


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

(* exemples *)
Theorem ttrue: Is_true true.
Proof.
  simpl.
  reflexivity.
Qed.

(* on verifie si la fonction andB rend faux pour
les deux parametres true et false qui et bien une
definition du cours pour et; /\*)
Theorem trueandtrue: (Is_true  (andB true false))->False.
Proof.
simpl.
intro.
assumption.
Qed.

(*
Lemma exB1: forall a b:bool, andB a b = true -> a = true /\ b = true.
Proof.
intros.
simpl.
*)

(* 3) ***** LK0, Definitions des regles  ******)
(*definition d'une formule*)
Open Scope list_scope.

Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
Fixpoint sum(l1 l2 : list nat) : (list nat) :=
  match l1 , l2 with
    |nil, nil => nil
    |e1 :: tl1, e2 :: tl2 => (e1 + e2) :: (sum tl1 tl2)
    | _, _ => nil
  end.

Inductive formule: Type:=
  | neg: bool->formule
  | et: bool->bool->formule
  | ou: bool->bool->formule
  | impl: bool->bool->formule
  | equiv: bool->bool->formule.
(*definition de l'hypothese qui est egalement 
un ensemble de formules*)
Print formule_ind.
Inductive eval: formule->bool->:=
  |Eneg: forall x : bool, eval (neg x) x.
Theorem ss: forall (X : bool), eval(neg X). 
  





