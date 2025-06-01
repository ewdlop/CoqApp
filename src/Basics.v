(** * Basic Definitions and Lemmas *)

(** This file contains fundamental definitions and basic proofs
    that serve as building blocks for more complex theorems. *)

(** ** Natural Numbers *)

(** We start with the standard inductive definition of natural numbers *)
Inductive nat : Type :=
| O : nat
| S : nat -> nat.

(** Addition on natural numbers *)
Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

(** Multiplication on natural numbers *)
Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => add m (mult n' m)
  end.

(** Notation for convenience *)
Notation "x + y" := (add x y) (at level 50, left associativity).
Notation "x * y" := (mult x y) (at level 40, left associativity).

(** ** Basic Properties *)

(** Addition is associative *)
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - (* n = O *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

(** Zero is the right identity for addition *)
Theorem add_0_r : forall n : nat, n + O = n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - (* n = O *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

(** Successor and addition *)
Theorem add_S_r : forall n m : nat,
  n + S m = S (n + m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - (* n = O *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

(** Addition is commutative *)
Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - (* n = O *)
    simpl. rewrite add_0_r. reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. rewrite add_S_r. reflexivity.
Qed.

(** ** Boolean Operations *)

(** Boolean type *)
Inductive bool : Type :=
| true : bool
| false : bool.

(** Boolean negation *)
Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(** Boolean AND *)
Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(** Boolean OR *)
Definition orb (b1 b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** Notation for boolean operations *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

(** ** Properties of Boolean Operations *)

(** Double negation *)
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intro b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

(** AND is commutative *)
Theorem andb_comm : forall b1 b2 : bool,
  b1 && b2 = b2 && b1.
Proof.
  intros b1 b2.
  destruct b1; destruct b2; reflexivity.
Qed. 