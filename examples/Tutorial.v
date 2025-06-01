(** * Coq Tutorial: Getting Started *)

(** This file provides a gentle introduction to Coq for beginners.
    It demonstrates basic concepts and proof techniques. *)

(** ** Basic Data Types *)

(** Coq has built-in support for various data types.
    Let's start with booleans. *)

Print bool.

(** We can define simple functions *)
Definition my_negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(** Let's test our function *)
Compute my_negb true.
Compute my_negb false.

(** ** Simple Proofs *)

(** Now let's prove that our negation function is involutive
    (applying it twice gives back the original value) *)

Theorem my_negb_involutive : forall b : bool,
  my_negb (my_negb b) = b.
Proof.
  intro b.           (* Introduce the variable b *)
  destruct b.        (* Consider both cases: b = true and b = false *)
  - simpl. reflexivity.  (* Case: b = true *)
  - simpl. reflexivity.  (* Case: b = false *)
Qed.

(** ** Working with Natural Numbers *)

(** Let's define a simple recursive function *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

(** Test our factorial function *)
Compute factorial 0.
Compute factorial 1.
Compute factorial 4.

(** ** Induction Proofs *)

(** Let's prove a simple property about addition *)
Theorem plus_n_O : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    simpl. reflexivity.
  - (* Inductive case: n = S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

(** ** Working with Lists *)

(** Import the standard library list *)
Require Import List.
Import ListNotations.

(** Define a simple function on lists *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | h :: t => h + sum_list t
  end.

(** Test our function *)
Compute sum_list [1; 2; 3; 4].

(** Prove a property about our sum function *)
Theorem sum_list_app : forall l1 l2 : list nat,
  sum_list (l1 ++ l2) = sum_list l1 + sum_list l2.
Proof.
  intros l1 l2.
  induction l1 as [| h t IH].
  - (* Base case: l1 = [] *)
    simpl. reflexivity.
  - (* Inductive case: l1 = h :: t *)
    simpl. rewrite IH.
    (* We need commutativity and associativity of + *)
    ring.  (* This tactic solves arithmetic goals *)
Qed.

(** ** Interactive Proof Development *)

(** When developing proofs interactively, you can use various tactics:
    
    - intro/intros: introduce hypotheses
    - destruct: case analysis
    - induction: proof by induction
    - simpl: simplify expressions
    - reflexivity: prove equality when both sides are the same
    - rewrite: use an equality hypothesis to rewrite the goal
    - apply: apply a theorem or hypothesis
    - exact: provide an exact proof term
    
    Try stepping through the proofs above using your Coq IDE! *)

(** ** Exercise for the Reader *)

(** Try to prove this theorem on your own: *)
Theorem sum_list_rev : forall l : list nat,
  sum_list (rev l) = sum_list l.
Proof.
  (* Your proof here! Hint: you might need to prove a helper lemma first *)
Admitted. 