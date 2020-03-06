(* $Id *)

(* Propositional Logic *)

Parameters A B C : Prop.

Lemma prop1 : A -> B -> A.
Proof.
  intros.
  assumption.
Qed.

Lemma prop2 : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  intros.
  apply H.
  assumption.
  apply H0.
  assumption.
Qed.

Lemma prop3 : A /\ B -> B.
Proof.
  intro.
  elim H; intros.
  assumption.
Qed.

Lemma prop4 : B -> A \/ B.
Proof.
  intro.
  right.
  assumption.
Qed.

Lemma prop5 : (A \/ B) -> (A -> C) -> (B -> C) -> C.
Proof.
  intros.
  elim H; intro.
  apply H0; assumption.
  apply H1; assumption.
Qed.

Lemma prop6 : A -> False -> ~A.
Proof.
  intros.
  elimtype False.
  assumption.
Qed.

Lemma prop7 : False -> A.
Proof.
  intro.
  elimtype False.
  assumption.
Qed.

Lemma prop8 : (A <-> B) -> (A -> B).
Proof.
  intro.
  elim H; do 2 intro.
  assumption.
Qed.

Lemma prop9 : (A <-> B) -> (B -> A).
Proof.
  intro.
  elim H; do 2 intro.
  assumption.
Qed.

Lemma prop10 : (A -> B) -> (B -> A) -> (A <-> B).
Proof.
  intros.
  split; assumption.
Qed.

(* First Order Logic *)

Parameter E : Set.
Parameter P Q : E -> Prop.

Lemma fol1 : forall x : E, (P x) -> exists y : E, (P y) \/ (Q y).
Proof.
  intro.
  intro.
  exists x.
  left.
  assumption.
Qed.

Lemma fol2 :
  (exists x : E, (P x) \/ (Q x)) ->
    (exists x : E, (P x)) \/ (exists x : E, (Q x)).
Proof.
  intro.
  elim H; intros.
  elim H0; intro.
  left.
  exists x.
  assumption.
  right.
  exists x.
  assumption.
Qed.

Lemma fol3 :
  (forall x : E, (P x)) /\ (forall x : E, (Q x)) ->
    forall x : E, (P x) /\ (Q x).
Proof.
  intro.
  intro.
  elim H; intros.
  split.
  apply H0.
  apply H1.
Qed.

Lemma fol4 :
  (forall x : E, (P x) /\ (Q x)) ->
    (forall x : E, (P x)) /\ (forall x : E, (Q x)).
Proof.
  intro.
  split; intro; elim (H x); intros; assumption.
Qed.

Lemma fol5 : (forall x : E, ~(P x)) -> ~(exists x : E, (P x)).
Proof.
  intro.
  intro.
  elim H0; intros.
  apply (H x).
  assumption.
Qed.

(* Le dernier problème ne peut être démontré qu'en logique classique *)
Require Export Classical.

Lemma fol6 : ~(forall x : E, (P x)) -> exists x : E, ~(P x).
Proof.
  intro.
  apply NNPP.
  intro.
  apply H.
  intro.
  apply NNPP.
  intro.
  apply H0.
  exists x.
  assumption.
Qed.
