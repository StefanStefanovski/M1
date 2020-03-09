Require Export ZArith.
Open Scope Z.

Inductive expr: Set :=
  | Cte: Z->expr
  | Plus: expr->expr->expr
  | Moins: expr->expr->expr
  | Mult: expr->expr->expr
  | Div: expr->expr->expr.

Inductive eval: expr -> Z -> Prop:=
  | ECte: forall c: Z, eval(Cte c) c
  | EPlus: forall (e1 e2 : expr) (v1 v2 v : Z),
    eval e1 v1 -> eval e2 v2 ->
    v = v1 + v2 -> eval (Plus e1 e2) v
  | EMoins: forall (e1 e2 : expr) (v1 v2 v : Z),
    eval e1 v1 -> eval e2 v2 ->
    v = v1 - v2 -> eval (Moins e1 e2) v
  | EMult: forall (e1 e2 : expr) (v1 v2 v : Z),
    eval e1 v1 -> eval e2 v2 ->
    v = v1 * v2 -> eval (Mult e1 e2) v
  | EDiv: forall (e1 e2 : expr) (v1 v2 v : Z),
    eval e1 v1 -> eval e2 v2 ->
    v = v1 / v2 -> eval (Div e1 e2) v.

Lemma ex1: eval (Plus (Cte 1) (Cte 2)) 3.
eapply EPlus.
apply ECte.
apply ECte.
auto.

Lemma ex2: eval (Mult (Cte 2) (Plus (Cte 2) (Cte 3))) 10.
eapply EMult.
apply ECte.
eapply EPlus.
apply ECte.
apply ECte.
auto.
auto.

Ltac MonEval:=
repeat (
  auto; match goal with
  | |- context [Cte _] => apply ECte
  | |- context [Plus _ _] => eapply EPlus
  | |- context [Moins _ _] => eapply EMoins
  | |- context [Mult _ _] => eapply EMult
  | |- context [Div _ _] => eapply EDiv
end).

Lemma ex2: eval (Mult (Cte 2) (Plus (Cte 2) (Cte 3))) 10.
MonEval.


Fixpoint f_eval (e : expr) : Z:=
  match e with
    |Cte c=>c
    |Plus e1 e2 =>
      let v1:= f_eval e1 in
      let v2:= f_eval e2 in
      v1+v2
    |Moins e1 e2 =>
      let v1:= f_eval e1 in
      let v2:= f_eval e2 in
      v1-v2
    |Mult e1 e2 =>
      let v1:= f_eval e1 in
      let v2:= f_eval e2 in
      v1*v2
    |Div e1 e2 =>
      let v1:= f_eval e1 in
      let v2:= f_eval e2 in
      v1/v2
end.

Lemma ex3: f_eval (Plus (Cte 2) (Cte 3)) = 5.
simpl.
reflexivity.

Lemma ex4: f_eval (Mult (Plus (Cte 2) (Cte 3)) (Cte 3)) = 15.
simpl.
auto.

Eval compute in (f_eval (Mult (Plus (Cte 2) (Cte 3)) (Cte 3))).
(*Require Import FunInd.*)

Functional Scheme f_eval_ind := Induction for f_eval Sort Prop.
Check f_eval_ind.

Lemma Correction: forall (e: expr) (v: Z), (f_eval e) = v-> eval e v.
Proof.
intro.
functional induction (f_eval e) using f_eval_ind; intros;
(rewrite H; MonEval) || MonEval.


















(*Ltac Teval:=
  simpl;
  reflexivity.


Lemma ex3: f_eval (Plus (Cte 2) (Cte 3)) = 5.
Teval.

Fixpoint MonEval
/*)