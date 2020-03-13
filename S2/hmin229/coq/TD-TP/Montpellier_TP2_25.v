Inductive is_even : nat->Prop :=
| is_even_O : is_even 0
| is_even_S : forall n : nat, is_even n->is_even (S(S n)).

Fixpoint even (n : nat) : Prop:=
match n with
| 0 => True
| 1 => False
| (S(S n)) => even n
end.

Functional Scheme even_ind := Induction for even Sort Prop.




Inductive is_fact : nat*nat->Prop :=
| is_fact_O : is_fact(0,1)
| is_fact_S : forall n s : nat, is_fact(n,s) -> is_fact(S n,s*(S n)).

Fixpoint fact (n : nat) : nat :=
match n with
| 0 => 1
| S p => (fact p) * n
end.

Functional Scheme fact_ind := Induction for fact Sort Prop.


Theorem fact_sound : forall (n p : nat), fact n = p -> is_fact(n,p).
Proof.
intro.
functional induction (fact n) using fact_ind; intros.
rewrite <- H. apply is_fact_O.
rewrite <-H. apply is_fact_S. apply IHn0. reflexivity.
Qed.


Require Export List.
Require Import Arith.
Open Scope list_scope.
Import ListNotations.

Inductive is_perm : (list nat)*(list nat) -> Prop :=
|is_perm_vide : is_perm([],[])
|is_perm_top : forall (a: nat) (l1: list nat) (l2: list nat), is_perm(l1,l2) -> is_perm(a::l1, a::l2)
|is_perm_back : forall (a: nat) (l: list nat), is_perm(a::l, l++[a])
|is_perm_refl : forall (l: list nat), is_perm(l,l)
|is_perm_trans : forall (l1: list nat) (l2: list nat) (l3: list nat), is_perm(l1,l2) -> is_perm(l2,l3) -> is_perm(l1,l3)
|is_perm_sym : forall (l1: list nat) (l2: list nat), is_perm(l1,l2) -> is_perm(l2,l1).

Goal is_perm([1;2;3],[3;2;1]).
Proof.
apply is_perm_trans with ([2;3]++[1]). apply is_perm_back.
apply is_perm_trans with ([3;1]++[2]). apply is_perm_back.
apply is_perm_top.
apply is_perm_trans with ([1]++[2]). apply is_perm_refl. apply is_perm_back.
Qed.

Inductive is_sort : (list nat) -> Prop :=
|is_sort_vide : is_sort([])
|is_sort_single : forall (a: nat), is_sort([a])
|is_sort_top : forall (n m: nat) (l: list nat), n<=m -> is_sort(m::l) -> is_sort(n::m::l).

Goal is_sort([1;2;3]).
Proof.
apply is_sort_top. auto.
apply is_sort_top. auto.
apply is_sort_single.
Qed.

Fixpoint insert (n: nat) (l: list nat) {struct l} : list nat :=
 match l with
 |[] => n::[]
 |m::l0 => match le_dec n m with
           |left _ => n::m::l0
           |right _ => m::(insert n l0)
           end
 end.

Fixpoint insert_tri (l: list nat) : list nat :=
 match l with
 |[] => []
 |n::l0 => insert n (insert_tri l0)
 end.



Theorem insert_tri_correct_match : forall (l1 l2: list nat), insert_tri(l1) = l2 -> is_perm(l1,l2) /\ is_sort(l2).
Proof.
induction l1.
intros. rewrite <- H. simpl. split. apply is_perm_vide. apply is_sort_vide.
intros. rewrite <- H. simpl. elim IHl1 with (insert_tri l1). intros.
split.



Qed.

case

Theorem insert_tri_correct_sort : forall (l: list nat), is_sort(insert_tri l).











