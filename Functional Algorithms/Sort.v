Require Import PeanoNat.
Require Import Permutation.
Require Import List.
Import ListNotations.
(* Require Import Perm. *)
(* insert i l inserts i into its sorted place in list l.
   Precondition: l is sorted. *)

Fixpoint insert (i : nat) (l : list nat) : list nat :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.
  
Example sort_pi :
  sort [3;1;4;1;5;9;2;6;5;3;5]
  = [1;1;2;3;3;4;5;5;5;6;9].
Proof.
  simpl. reflexivity.
Qed.
  
Compute insert 7 [1;3;4;8;12;14;18].

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_1 : forall x, sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).


Definition sorted'' (al : list nat) := forall i j,
  i < j < length al ->
  nth i al 0 <= nth j al 0.

Definition sorted' (al : list nat) := forall i j iv jv,
  i < j ->
  nth_error al i = Some iv ->
  nth_error al j = Some jv ->
  iv <= jv.
  
Definition is_a_sorting_algorithm (f : list nat -> list nat) := forall al,
  Permutation al (f al) /\ sorted (f al).

Theorem insert_sorted:
  forall a l, sorted l -> sorted( insert a l).
Proof.
  intros a l S. induction S. simpl.
Qed.
  
  
  
  
  
  
  
  
  
  
  