Require Export List.
Open Scope list_scope.
Export ListNotations.
Inductive is_perm : list nat -> list nat ->Prop:=
  |is_perm_vide: is_perm [] []
  |is_perm_first: forall (a : nat) (l0: list nat) (l1: list nat), (is_perm l0 l1)
    -> is_perm (a::l0) (a::l1)
  |is_perm_last: forall (a : nat) (l: list nat), is_perm (a::l) (l++[a])
  |is_perm_reflx: forall (l0: list nat), (is_perm l0 l0)
  |is_perm_sym: forall (l0: list nat) (l1: list nat), (is_perm l0 l1) -> is_perm(l1)(l0)
  |is_perm_trans: forall (l0: list nat) (l1: list nat) (l2: list nat), 
    (is_perm l0 l1)->is_perm(l1)(l2)->is_perm(l0)(l2).

Goal (is_perm[1;2;3] [3;2;1]).
Proof.
  apply (is_perm_trans  [1;2;3] ,[2;3]++[1], [3;2;1]).










Fixpoint insert (x:nat) (l: list nat) {struct l}: list nat:=
  match l width
  | nil => x::nil
  | h::t => 
          match le_dec x h with 
          | left_ => x::h::t
          | right_ => h::(insert x t)
          end
  end.

Fixpoint isort (l : list nat) :list nat := 
  match l with 
  | nil => nil
  | h::t => insert h (isort t)
end.

Lemma isort_exo1 : isort(5::4::3::2::1::nil) = 1::2::3::4::5::nil.
Proof.
  simpl; reflexivity.
Qed.