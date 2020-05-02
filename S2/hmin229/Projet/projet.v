Variables A B C: Prop.
(* 1 ==>  **** Exemples de formules de proposition****)

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

(****** preuves d'associativité a gauche *****)
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
  

(* Definition de type boolean (bool) pour les valeurs 
de variables de propositions qui peut être vrai ou faux *)

Inductive bool : Type :=
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
    left; reflexivity.
  (* deuxieme cas b est false*)
    right; reflexivity.
Qed. 

(* Ici nous avons ajouté des definitions pour le type bool qui 
  rendent une proposition true est True (vrai) et false est False (faux) *)

Inductive False : Prop := .
Inductive True : Prop :=
| I : True.


Definition Is_true (b:bool) :=
  match b with
    | true => True
    | false => False
  end.

(* Definitions de fonctions B x B vers B; (B: boolean) *)

Definition negB (b1 : bool) : bool :=
  match b1 with
    | false => true
    | true => false
  end.
Definition andB (b1 b2 : bool) :=
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
Definition implB (b1 b2 : bool) : bool :=
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

(* Verification si la fonction andB rend faux pour
les deux parametres true et false qui et bien une
definition du cours pour et; /\*)
Theorem exB: (Is_true  (andB true false))->False.
Proof.
  simpl.
  intro.
  assumption.
Qed.

(* test pour la fonction ou \/ *)
Lemma exB1: forall a b :bool, orB a true =  true.
Proof.
  intros.
  elim a.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.
(* test pour equivalent <-> *)
Lemma eqb_reflx : forall b:bool, equivB b b = true.
Proof.
  intros.
  elim b.
  simpl.
  reflexivity.
  simpl; reflexivity.
Qed.

(* !!!!!!!!!! Manques des tests pour implication et negation  !!!!!!!!
            TO DO!!!! *)

(* ******************  2    ******************)
(*******  Definitions de formules  ******)
Inductive formule: Set:=
  | P: bool->formule
  | neg: bool->formule
  | et: formule->formule->formule
  | ou: formule->formule->formule
  | impl: formule->formule->formule
  | equiv: formule->formule->formule.

(******* Evaluation d'une formule *********)
Inductive evalFormule: formule -> bool -> Prop:=
  | EP: forall c: bool, evalFormule(P c) c

  | Eneg: forall c: bool, evalFormule(neg  c) (negB c)

  | Eand: forall (e1 e2 : formule) (v1 v2 v : bool),
    evalFormule e1 v1 -> evalFormule e2 v2 ->
    v = andB v1 v2 -> evalFormule (et e1 e2) v

  | Eor: forall (e1 e2 : formule) (v1 v2 v : bool),
    evalFormule e1 v1 -> evalFormule e2 v2 ->
    v = orB v1 v2 -> evalFormule (ou e1 e2) v

  | Eimpl: forall (e1 e2 : formule) (v1 v2 v : bool),
    evalFormule e1 v1 -> evalFormule e2 v2 ->
    v = implB v1 v2 -> evalFormule (impl e1 e2) v

  | Eequiv: forall (e1 e2 : formule) (v1 v2 v : bool),
    evalFormule e1 v1 -> evalFormule e2 v2 ->
    v = equivB v1 v2 -> evalFormule (equiv e1 e2) v.

(* Exemples *)

Lemma test: evalFormule ( et ( P true) (P true) ) true.
Proof.
  eapply Eand.
  apply EP.
  apply EP.
  simpl.
  reflexivity.
Qed.
Lemma test1: evalFormule (neg  true) false.
Proof.
  eapply Eneg.
Qed.

(*  
  !!!!!!!!!!!! TO DO !!!!!!!!!!!!!!!!! 

Pour l'instant la negation marche que avec des
propositions et pas avec une formule, on a pas encore 
definit la transomation
Lemma test2: evalFormule (neg et (P true) (P false)) true.
et ajouter des exemples*)

(* definition d'une tactic qui verifie si l'interpretation donnée 
est un modèle de la formule *) 
Ltac modele :=
repeat(
   auto; match goal with
  | |- context [P _] => apply EP
  | |- context [et _ _] => eapply Eand
  | |- context [ou _ _] => eapply Eor
  | |- context [impl _ _] => eapply Eimpl
  | |- context [equiv _ _] => eapply Eequiv
end).

(**** Exemple ****)
Lemma test5: evalFormule ( et ( P true) (P true) ) true.
Proof.
  modele.
Qed.






(*definition de l'hypothese qui est egalement 
un ensemble de formules*)
Print formule_ind.
Inductive eval: formule->bool->:=
  |Eneg: forall x : bool, eval (neg x) x.
Theorem ss: forall (X : bool), eval(neg X). 



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


  





