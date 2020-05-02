(* $Id$ *)

Require Import FunInd.

Inductive is_even : nat -> Prop :=
| is_even_O : is_even 0
| is_even_S : forall n : nat, is_even n -> is_even (S (S n)).

Fixpoint even (n : nat) : Prop :=
  match n with
  | 0 => True
  | 1 => False
  | (S (S n)) => even n
  end.

Functional Scheme even_ind := Induction for even Sort Prop.

Theorem even_sound : forall (n : nat) (v : Prop), (even n) = True -> is_even n.
Proof.
  do 2 intro.
  functional induction (even n) using even_ind; intros.
  apply is_even_O.
  elimtype False; rewrite H; auto.
  apply is_even_S; apply IHP; assumption.
Qed.
