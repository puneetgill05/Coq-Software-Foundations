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

Fixpoint even (n : nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool :=
  negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (plus n' m)
  end.
  
Compute (plus 3 2).


Fixpoint mult (n m : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | 0, _ => 0
  | S _, 0 => n
  | S n', S m' => minus n' m'
  end.
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | 0 => S 0
  | S p => mult base (exp base p)
  end.
  
  Fixpoint factorial (n:nat) : nat :=
    match n with
    | 0 => 1
    | S n' => (NatPlayground2.mult (S n') (factorial n'))
    end.
    
  Example test_factorial1: (factorial 3) = 6.
  Proof. simpl. reflexivity. Qed.
  Example test_factorial2: (factorial 5) = (mult 10 12).
  Proof. simpl. reflexivity. Qed.

  
Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                      : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                      : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                      : nat_scope.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | 0 => match m with
      | 0 => true
      | S m' => false
      end
  | S n' => match m with
      | 0 => false
      | S m' => eqb n' m'
      end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | 0 => true
  | S n' => match m with
    | 0 => false
    | S m' => leb n' m'
    end
  end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.


Definition ltb (n m : nat) : bool :=
  andb (leb n m) (negb (eqb n m)).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_0_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_0_n'' : forall n : nat,
  0 + n = n.
Proof.
  intros m. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof. intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.

Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity. Qed.
  
Check mult_n_O.

Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.
  
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n +1) =? 0 = false.

Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c,
  andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb3_exchange : forall b c d,
  andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c eqn:Ec.
    - reflexivity.
    - rewrite <- H.
      destruct b.
      reflexivity. reflexivity.
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'' : forall b c,
  andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
  
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.









