Open Scope nat_scope.

Inductive is_even: nat -> Prop:= 
  | is_even_O: is_even O
  | is_even_S: forall n: nat, 
    is_even n -> is_even(S (S n)).

Goal is_even 2.

apply is_even_S.
apply is_even_O.

Goal ~is_even 3.

intro.
inversion H.
inversion H1.

Ltac Teven:=
  repeat 
    apply is_even_S || apply is_even_O.

Goal is_even 14.
Teven.


Ltac notTeven:=   
  intro;
  repeat 
    match goal with
    | H: is_even  |-_ => inversion H
  end.

Goal ~is_even 13.

notTeven.


  
Lemma exo1: forall n



