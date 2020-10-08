(* Stefan Stefanovski 
  Hamza Raghbib *)



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


(*
4) Montrons que le système LK est correct. 

Par induction sur la dérivation du séquent ∆ ├  Γ dans le 
système G à l'aide de la réversibilité et du fait que les axiomes 
sont des séquents valides. Pour développer cette preuve on utilise la notation
 ∆ ⇒ Γ pour la formule associée au séquent ∆ ├ Γ (même si ∆ ⇒ Γ n'est pas 
proprement une formule). 

Cas de base : 
La dérivation est de la forme  
 
                                                    _______________(ax)
                                                       ∆’ , A ├ Γ’, A
                                                                                             
Alors on montre que ∆’ ∧ A ⇒ Γ’ ∨ A est valide par coq.

Si ∆’ = B et Γ’ = C on a 

Theorem Cas_base : (forall A B C : Prop,
(B→ C)→ ((A /\ B) →  (C \/ A))).
Proof.
intros.
elim H0.
right; assumption.
Qed.

Si ∆’ = B /\ D et Γ’ = C \/ E on a par coq toujours. 

∆’ ∧ A ⇒ Γ’ ∨ A est valide.
*)
Theorem Cas_base_2 : (forall A B C D E : Prop,
((B/\D) -> (C\/E))-> ((B /\ D /\ A) -> (C \/ D \/ A))).
Proof.
intros.
elim H0.
intros.
elim H2.
intros.
right.
right.
assumption.
Qed.
(*
Donc par récurrence on peut montrer que pour n’import quelle formule ∆’ et Γ’ 
on a ∆├ Γ.


Les cas inductifs :
1er cas )      
La dérivation est de la forme                                                     .
                                                                                                   . 
                                                                                        ______________
                                                                                             ∆’ , A ,B├ Γ 
                                                                                          ______________( ˄gauche) 
                                                                                             ∆’ , A ˄ B├ Γ     



On montre que ∆’ , A ∧ B ⇒ Γ est valide

*)
Theorem Cas_induc_ 1 : (forall A B C D  : Prop,
(D → C )→  ((D /\( B /\ A)) →  C)).
Proof.
intros.
elim H0.
intros.
elim H2.
elim H0.
intros.
apply H.
apply H1.
Qed.

∆’ , A ∧ B ⇒ Γ est valide.

2eme cas inductif) 
La dérivation est de la forme 

                  .                     .
                  .                     .
            ________       _________
            ∆’ , A ├ Γ       ∆’ , B ├ Γ
           _______________________ (˅gauche)
                      ∆’ , A ˅ B ├ Γ
    

de continue de cette manière pour prouver la validité des cas inductifs 
(on trouve qu’ils sont valides) ce qui prouve que le système LK est correct.
5)
Montrons que le système LK est complet.

Pour montrer que le système LK est complet, on construit une dérivation ∆ ├ LK Γ 
dans le système LK sans coupures, ceci en prenant comme racine le séquent ∆├  Γ 
et en appliquant les règles du système du bas vers le haut aussi longtemps 
que possible. Ce processus s'arrête nécessairement car tout séquent prémisse 
est "plus petit" que le séquent conclusion (propriété de sous-formule). 
En plus, comme le séquent de la racine est valide, tous les séquents 
introduits par cette construction sont valides d'après le théorème de 
réversibilité. 
Pour conclure il faut montrer que la construction s'arrête sur des séquents 
axiomes, c'est à dire, que toute feuille de l'arbre de dérivation est un axiome. 
Pour ceci on raisonne par l'absurde. Si le séquent d'une feuille contient encore 
un connecteur logique, alors on peut toujours appliquer une règle du système, 
ce qui est en contradiction avec le fait que c'était une feuille. 
Alors, si le séquent d'une feuille n'a plus de connecteur logique mais 
il n'est pas un axiome, c'est qu'il est de la forme p1, . . . , pm ├ q1, . . . qn . 
avec pi ≠ qj , pour tout i, j. 
L'interprétation qui donne vrai à toutes les lettres pi et faux à toutes les 
lettres qj falsifie ce séquent, ceci est une contradiction avec le fait que ce 
séquent soit valide. 
*)


