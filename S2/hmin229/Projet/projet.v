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
  | neg: formule->formule
  | et: formule->formule->formule
  | ou: formule->formule->formule
  | impl: formule->formule->formule
  | equiv: formule->formule->formule.

(******* Evaluation d'une formule *********)
Inductive evalFormule: formule -> bool -> Prop:=
  | EP: forall c: bool, evalFormule(P c) c

  | Eneg: forall (e1: formule) (v1 v :bool), 
    evalFormule e1 v1 -> v = negB v1 -> evalFormule (neg e1) v

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

Lemma ttt: evalFormule (neg (P true)) false.
Proof.
  eapply Eneg.
  apply EP.
  simpl.
  reflexivity.
Qed.


Lemma test1: evalFormule (et (P true) (neg ( (P true)))) false.
Proof.
  eapply Eand.
  apply EP.
  eapply Eneg.
  apply EP.
  auto.
  reflexivity.
Qed.

 
Lemma test: evalFormule ( et ( P true) (P true) ) true.
Proof.
  eapply Eand.
  apply EP.
  apply EP.
  simpl.
  reflexivity.
Qed.


(* definition d'une tactic qui verifie si l'interpretation donnée 
est un modèle de la formule *) 
Ltac modele :=
repeat(
   auto; match goal with
  | |- context [P _] => apply EP
  | |- context [neg _] => eapply Eneg
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

(* Dans le cas où nous souhaitons prouver que ce n'est pas un modele 
  cela est fait en remplacant le resultat true par false voir l'exemple d'un
  contre modèle ci dessous pour la formule précédente *)
Lemma test51: evalFormule ( et ( P true) (P false) ) false.
Proof.
  modele.
Qed.

(* formule valide exemple de l'enonce *)
Lemma test6: forall a b :bool, evalFormule (impl( et ( P a) (P b) ) (P a)) true.
Proof.
  intro.
  intro.
  destruct a. (* pour a vrai et faux // avec elim c'est possible aussi*)
  destruct b. (* pour b vrai et faux *)
  modele. (* est-ce que c'est un modele? *)
  modele.
  destruct b.
  modele.
  modele.
Qed.

(* VALIDE, INSATISFIABLE ou SATISFIABLE;
 
  | Pour verifier si une formule est valide nous avons crée une tactique valide qui verifie
    si la formule est vrai pour toutes interpretations. 
    Donc pour la formuler:
  
      --- forall x :bool, evalFormule( (...) true ) apres appliquer la tactique valide;

    si la tactique se termine sans erreur et sans 'subgoals' c'est a dire que la formule est valide et satisfiable,

  | Pour verifier si une formule est insatisfiable, la tactique valide permet également 
    de vérifier cette propriété  en considerant que cette fois ci le test est fait si la 
    formule est fausse pour toutes interpretations.
    Donc pour la formuler:

      --- evalFormule( (...) false ) apres appliquer la tactique valide
   
    si la tactique se termine sans erreur et sans 'subgoals' c'est a dire que la formule est insatisfiable*)
Ltac destruct_all t :=
 match goal with
  | x : t |- _ => destruct x; destruct_all t
  | _ => idtac
 end.
Ltac valide := 
  intros; destruct_all bool; repeat modele.


Lemma test8: forall a b :bool, evalFormule (impl( et ( P a) (P b) ) (P a)) true.
Proof.
  valide.
Qed.

(* exemple de l'enonce A et non A *)
Lemma test10: forall  a : bool, evalFormule (et (P a) (neg (P a))) false.
Proof.
  valide.
Qed.

Lemma test7: forall a b :bool, evalFormule (impl( et ( P a) (P b) ) (P a)) true.
Proof.
  valide.
Qed.


(* ************** LK *************** *)

Open Scope list_scope.

Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Inductive sequence: Set :=
  | Gamma : list formule->sequence
  | Delta : list formule->sequence.

Inductive regles: Set->Prop :=
  | ax: forall G D: sequence,   
(*definition de l'hypothese qui est egalement 
un ensemble de formules*)
Definition tl (l:list formule) :=
    match l with
      | [] => nil
      | a :: m => m
    end.

Fixpoint sum(l1 l2 : list nat) : (list nat) :=
  match l1 , l2 with
    |nil, nil => nil
    |e1 :: tl1, e2 :: tl2 => (e1 + e2) :: (sum tl1 tl2)
    | _, _ => nil
  end.


  





