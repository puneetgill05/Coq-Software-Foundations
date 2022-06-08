Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
end.

Compute (next_weekday friday).
Compute (next_weekday(next_weekday friday)).

Example test_next_weekday: (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

From Coq Require Export String.

Inductive bool: Type :=
  | true
  | false.

Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
end.

Definition andb (b₁: bool) (b₂ : bool) : bool := 
  match b₁ with
  | true => b₂
  | false => false
end.

Definition orb (b₁: bool) (b₂ : bool) : bool := 
  match b₁ with
  | true => true
  | false => b₂
end.


Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.


Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.


Definition negb' (b: bool) : bool :=
  if b then false
  else true.

Definition andb' (b₁: bool) (b₂: bool) : bool :=
  if b₁ then b₂
  else false.

Definition orb' (b₁: bool) (b₂: bool) : bool :=
  if b₁ then true
  else b₂.


Definition nandb (b₁:bool) (b₂:bool) : bool := 
  if b₁ then (negb b₂)
  else true.


Example test_nand1: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nand2: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nand3: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nand4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.



Definition andb3 (b₁:bool) (b₂:bool) (b₃:bool) : bool :=
  if (andb (andb b₁ b₂) b₃) then true
  else false.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check (negb true).
Check negb.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c: color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c: color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Module Playground.
  Definition b : rgb := blue.
End Playground.

Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.

Module TuplePlayground.
  Inductive bit : Type :=
    | B₀
    | B₁.

  Inductive nybble : Type :=
    | bits (b₀ b₁ b₂ b₃ : bit).

  Check (bits B₁ B₀ B₁ B₀) : nybble.

  Definition all_zero (nb : nybble) : bool :=
    match nb with
    | (bits B₀ B₀ B₀ B₀) => true
    | (bits _ _ _ _) => false
    end.

  Compute (all_zero (bits B₁ B₀ B₁ B₀)).
  Compute (all_zero (bits B₀ B₀ B₀ B₀)).
End TuplePlayground.


Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).

  Inductive nat' : Type :=
    | stop
    | tick (foo : nat').
    
  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
End NatPlayground.


Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
  | 0 => 0
  | S 0 => 0
  | S (S n') => n'
  end.

Compute (minustwo 4).


Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.


















