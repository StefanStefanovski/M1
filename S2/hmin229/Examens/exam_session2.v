(* Exo 1 *)

Parameter E : Set.
Parameters P Q : E -> Prop.
Parameter a : E.

Lemma question11 : (forall x, (P x) -> (Q x)) -> (P a) -> (Q a).
Proof.
  intros.
  apply H.
  assumption.
Qed.

Lemma question12 : (exists x, (P x) /\ (Q x)) -> (exists x, (P x)) /\ (exists x, (Q x)).
Proof.
  intro.
  elim H.
  intros.
  elim H0.
  intros.
  split.
  exists x.
  assumption.
  exists x.
  assumption.
Qed.

(* Exo 2 *)

Fixpoint eq_nat n m : Prop :=
  match n, m with
    | O, O => True
    | O, S _ => False
    | S _, O => False
    | S n1, S m1 => eq_nat n1 m1
  end.

Lemma question21 : forall (n : nat), eq_nat n n.
Proof.
  intros.
  induction n.
  simpl.
  auto.
  simpl.
  assumption.
Qed.

Lemma question22 : forall (n m : nat), n = m -> eq_nat n m.
Proof.
  intros.
  rewrite H.
  apply question21.
Qed.


(* Exo 3 *)

Require Export List.
Open Scope list_scope.
Import ListNotations.

Inductive is_rev : list nat -> list nat -> Prop :=
| is_rev_nil : is_rev nil nil
| is_rev_cons : forall (n : nat) (l1 l2 v : list nat), is_rev l1 l2 -> v = l2 ++ [n] -> is_rev (n::l1) v
| is_rev_sym : forall (l1 l2 : list nat), is_rev l1 l2 -> is_rev l2 l1.

Lemma exo3_1 : is_rev [1;2] [2;1].
Proof.
  apply is_rev_cons with [2].
  apply is_rev_cons with nil.
  apply is_rev_nil.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.