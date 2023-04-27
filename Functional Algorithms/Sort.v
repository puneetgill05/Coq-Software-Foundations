Require Import List.
(* Require Import Perm. *)
(* insert i l inserts i into its sorted place in list l.
   Precondition: l is sorted. *)

Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.
