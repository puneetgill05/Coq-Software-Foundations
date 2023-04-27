Require Import Nat.
Require Import Arith.Le.
Require Import Arith.Compare_dec.
Require Import Lia.
Require Import Lists.List.
Require Import Bool.Bool.


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
    i < j -> not (k - 3 <= j) -> k > i.
Proof.
  intros.
  Search (not _<=_ _->_).
  apply not_le in H0.
  Search (_<_ -> _<_ -> _<_).
  apply Nat.lt_trans with j.
  apply Nat.lt_trans with (k-3).
  Abort.

Theorem trucated_subtraction: not (forall k : nat, k > k-3).
Proof.
  intros contra.
  specialize (contra 0).
  simpl in contra.
  inversion contra.
Qed.

Theorem lia_exampl1: forall i j k,
  i < j -> not (k-3 <= j) -> k > i.
Proof.
  intros.
  apply not_le in H0.
  unfold gt in H0.
  unfold gt.
  Search (_<_ -> _<=_ -> _<_).
  apply Nat.lt_le_trans with j.
  apply H.
  apply le_trans with (k-3).
  Search (_<_ -> _<=_).
  apply Nat.lt_le_incl.
  auto.
  apply Nat.le_sub_l.
Qed.

Theorem lia_example2:
  forall i j k,
    i < j -> not (k-3 <= j) -> k > i.
Proof.
  intros.
  lia.
Qed.

Definition maybe_swap (al: list nat) : list nat :=
  match al with
  | a :: b :: ar => if a >? b then b :: a :: ar else a :: b :: ar
  | _ => al
  end.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Example maybe_swap_123: maybe_swap [ 1; 2; 3 ]= [ 1; 2; 3 ].
Proof. reflexivity. Qed.

Example maybe_swap_321: maybe_swap [ 3; 2; 1 ]= [ 2; 3; 1 ].
Proof. reflexivity. Qed.

Theorem maybe_swap_idemptotent: 
  forall al, maybe_swap (maybe_swap al) = maybe_swap al.
Proof.
  intros [ | a [ | b al]]. simpl. try reflexivity. reflexivity.
  destruct (a >? b) eqn:H1; simpl.
  - destruct (b >? a) eqn:H2. simpl.
    + Fail lia.
  Abort.

Print reflect.

Check (1+2 = 3).
Check (forall x: nat, exists y, x = y+y).

Check iff_reflect : forall (P: Prop) (b : bool),
  P <-> b = true -> reflect P b.

Print Nat.eqb_eq.

Lemma eqb_reflect: forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Check Nat.ltb_lt.

Lemma ltb_reflect: forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Check Nat.leb_le.
Lemma leb_reflect: forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Check Nat.ltb_lt.

Lemma gtb_reflect: forall x y, reflect (x > y) (x >? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma geb_reflect: forall x y, reflect (x >= y) (x >=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Example test_ltb1: (Nat.ltb 2 6) = true.
Proof.
  reflexivity.
Qed.

Example reflect_example1: forall a,
  (if a <? 5 then a else 2) < 6.
Proof.
  intros a.
  destruct (ltb_reflect a 5). lia. lia.
Qed.

Example reflect_example2: forall a,
  (if a <? 5 then a else 2) < 6.
Proof.
  intros a.
  assert (R: reflect (a < 5) (a <? 5)) by apply ltb_reflect.
  remember (a <? 5) as guard.
  destruct R as [H|H] eqn:HR.
  - lia.
  - lia.
Qed.

Hint Resolve ltb_reflect leb_reflect gtb_reflect geb_reflect eqb_reflect :
destruct.




























