Require Export Basics.
Require Import Compare_dec.
Require Import PeanoNat.
Require Import Unicode.Utf8.
Require Import Arith.Le.
Require Import Peano.

Theorem add_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
  (* Todo: 0 + m = m + 0 
     Todo: S n' + m = m + S n' *)
  simpl.
  rewrite -> add_0_r. reflexivity.
  (* Proved: 0 + m = m + 0 *)
  (* Todo: S n' + m = m + S n' *)
  induction m as [| m' IHm'].
  (* Todo: Sn' + 0 = 0 + Sn'
     Todo: Sn' + Sm' = Sm' + Sn' *)
  rewrite -> add_0_r.
    simpl. reflexivity.
  (* Proved: S n' + 0 = 0 + S n' *)
  (* Todo: Sn' + Sm' = Sm' + Sn' *)
  simpl. rewrite -> IHn'.
  (* Todo: S (S m' + n') = S (m' + S n') *)
  simpl.
  rewrite -> plus_n_Sm. reflexivity.
  (* Proved: S (S m' + n') = S (m' + S n') *)
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  (* Todo: 0 + (m + p) = 0 + m + p
     Todo: S n' + (m + p) = S n' + m + p *)
  - reflexivity.
  (* Proved: 0 + (m + p) = 0 + m + p
     Todo: S n' + (m + p) = S n' + m + p *)
  - simpl.
    rewrite -> IHn'.
    reflexivity.
  (* Proved: S n' + (m + p) = S n' + m + p *)
Qed.

Fixpoint double (n: nat) :=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.
  
Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Lemma double_plus: forall n, double n = n + n.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - { rewrite -> IHn'.
      simpl.
      rewrite -> negb_involutive.
      reflexivity. }
Qed.

Theorem mult_0_plus' : forall n m : nat,
(0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.


Theorem plus_rearrange_firsttry : forall n m p q : nat,
(n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  {rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.
Qed.

Theorem add_assoc' : forall n m p : nat, 
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - (* n  = 0 *)
  reflexivity.
  - (* n = S n' *)
  simpl. rewrite IHn'. reflexivity.
Qed.


Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  - (* n = 0 *)
  reflexivity.
  - (* n = S n' *)
  simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_comm.
  rewrite <- add_assoc.
  assert (H: p + n = n + p).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.
Qed.

Theorem mul_n_1 : forall n : nat,
  n * 1 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Lemma succ_R : forall m n : nat,
  m * S n = m + m * n.
Proof.
  intros m n. induction m as [|m' IHm'].
  - (* 0 * Sn = 0 + 0 * n *)
    simpl. reflexivity.
  - (* S m' * S n' = S m' + S m' * n *)
    simpl. rewrite -> IHm'. rewrite add_shuffle3. 
    reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction n as [|n' IHn'].
  - (* m * 0 = 0 * m *)
  rewrite mul_0_r. reflexivity.
  - (* m * S n' = S n' * m *)
  simpl. rewrite succ_R. rewrite IHn'.
  reflexivity.
Qed.
  
Check leb.
Check le_Sn_le.
Check plus_n_O.
Check PeanoNat.Nat.le_succ_r.

Theorem p_0_le_p_m : ∀ p m : nat,
  p + 0 ≤ p + m.
Proof.
  intros p m. induction p as [|p' IHp'].
  - simpl. rewrite le_0_n. reflexivity.
  - rewrite plus_Sn_m. simpl. rewrite PeanoNat.Nat.le_succ_l. simpl.  rewrite <- plus_n_O. 
    rewrite IHp'.


  - rewrite <- plus_n_O. induction m as [|m' IHm']. 
    + rewrite <- plus_n_O. reflexivity.
    + simpl. rewrite IHm'. simpl. rewrite plus_n_Sm.
      auto. 
    rewrite IHp'. rewrite add_0_r. rewrite <- IHp'. rewrite le_n_Sn. reflexivity.

Qed.


Theorem plus_leb_compact_l : ∀ n m p : nat,
  n <=? m = true → (p + n) <=? (p + m) = true.
Proof.
  intros n m p. induction n as [| n' IHn'].
  -  simpl.  . 
  -  simpl.
Qed.


Theorem Sk_eq_1_plus_k: ∀ k: nat,
  S k = 1 + k.
Proof.
  intros k.
  simpl. reflexivity.  
Qed.


Theorem n_mul_1_plus_k: forall n k : nat,
  n * (1 + k) = n + n * k.
Proof.
  intros n k.
  induction n as [| n' IHn'].
  - (* n = 0 *)
  simpl. reflexivity.
  - (* n = S n' *)
  rewrite plus_n_Sm.
  simpl. rewrite plus_n_Sm, add_comm.
  simpl. rewrite plus_n_Sm, plus_n_Sm, plus_n_Sm. simpl.
  rewrite Sk_eq_1_plus_k. rewrite IHn'.
  simpl.
  rewrite add_assoc'.
  rewrite <- plus_n_Sm. rewrite (add_comm n'*k k). simpl.

Qed.


Qed.



Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  rewrite 
  



