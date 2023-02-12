Module NatList.

Inductive natprod : Type := 
  | pair (n_1 n_2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p: natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p: natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x, y) => x
  end.

Definition snd' (p :  natprod) : nat :=
  match p with
  | (x, y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.
  
Theorem surjective_pairing_stuck : forall (p : natprod), p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(* Exercise *)
Theorem snd_fst_is_swap : forall (p : natprod), (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p. simpl. reflexivity. Qed.

(* Exercise *)
Theorem fst_swap_is_snd : forall (p : natprod), fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p. simpl. reflexivity. Qed.

(* List of Numbers *)
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l: natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
 (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Notation "x + y" := (plus x y)
  (at level 50, left associativity).
  
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | 0 => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => 0
  | h :: t => S (length t)
  end.

Fixpoint app (l₁ l₂ : natlist) : natlist :=
  match l₁ with
  | nil => l₂
  | h :: t => h :: (app t l₂)
  end.

Notation "x ++ y" := (app x y)
  (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.
  
Definition hd (default : nat) (l: natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l: natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd₁ : hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
























  



  
  
  
  
  



