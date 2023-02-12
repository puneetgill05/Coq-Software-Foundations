Require Import Nat.

Locate "_<_". (* "x < y" := lt x y *)
Check lt : nat -> nat -> Prop.

Locate "_<?_". (* x <? y := Nat.ltb x y *)
Check Nat.ltb : nat -> nat -> bool.

(* Check ltb_lt : forall n m : nat, (n < m) = true <-> n < m. *)

Print lt.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | 0 => true
  | S n' => match m with
            | 0 => false
            | S m' => leb n' m'
            end
  end.

(* Notation "x <=? y" := (leb x y) (at level 70) : nat_scope. *)

Definition geb (n m: nat) := m <=? n.
Hint Unfold geb : core.
Infix ">=?" := geb (at level 70) : nat_scope.

Definition gtb (n m : nat) := m <? n.
Hint Unfold gtb : core.
Infix ">?" := gtb (at level 70) : nat_scope.


Theorem lia_example1:
  forall i j k,
    i < j -> 