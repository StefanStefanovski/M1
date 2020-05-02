(* $Id$ *)

Require Import FunInd.

Inductive is_fact : nat -> nat -> Prop :=
| is_fact_O : is_fact 0 1
| is_fact_S : forall n m v : nat, is_fact n m -> v = (S n) * m -> is_fact (S n) v.

Lemma ex : is_fact 3 6.
Proof.
  eapply is_fact_S.
  eapply is_fact_S.
  eapply is_fact_S.
  apply is_fact_O.
  auto.
  auto.
  auto.
Qed.

Fixpoint fact (n : nat) : nat :=
  match n with
  | 0 => 1
  | (S n) => (S n) * (fact n)
  end.

Functional Scheme fact_ind := Induction for fact Sort Prop.

(* Check fact_ind.
fact_ind
     : forall P : nat -> nat -> Prop,
       (forall n : nat, n = 0 -> P 0 1) ->
       (forall n n0 : nat,
        n = S n0 -> P n0 (fact n0) -> P (S n0) (S n0 * fact n0)) ->
       forall n : nat, P n (fact n)*)

Theorem fact_sound : forall (n v : nat), (fact n) = v -> is_fact n v.
Proof.
(* Proof with an explicit application of fact_ind :
  intro; apply (fact_ind (fun (n v : nat) => forall v : nat, fact n = v -> is_fact n v));
    cbv beta iota delta [fact]; fold fact.
  intros; rewrite <- H; apply is_fact_O.
  intros; rewrite <- H0; eapply is_fact_S; auto.*)

  intro; functional induction (fact n) using fact_ind.
  intros; rewrite <- H; apply is_fact_O.
  intros; rewrite <- H; eapply is_fact_S; auto.
Qed.
