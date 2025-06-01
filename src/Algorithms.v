(** * Verified Algorithms *)

(** This file contains implementations of common algorithms
    with formal correctness proofs. *)

(** ** Lists *)

(** Inductive definition of lists *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.

(** Notation for lists *)
Notation "[ ]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "x :: l" := (cons x l) (at level 60, right associativity).

(** ** List Operations *)

(** Length of a list *)
Fixpoint length {A : Type} (l : list A) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

(** Append operation *)
Fixpoint app {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Notation "x ++ y" := (app x y) (at level 60, right associativity).

(** Reverse operation *)
Fixpoint rev {A : Type} (l : list A) : list A :=
  match l with
  | nil => nil
  | cons h t => (rev t) ++ [h]
  end.

(** ** Properties of List Operations *)

(** Length of append *)
Theorem length_app : forall {A : Type} (l1 l2 : list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros A l1 l2.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** Append is associative *)
Theorem app_assoc : forall {A : Type} (l1 l2 l3 : list A),
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros A l1 l2 l3.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** Nil is right identity for append *)
Theorem app_nil_r : forall {A : Type} (l : list A),
  l ++ nil = l.
Proof.
  intros A l.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** ** Insertion Sort *)

(** Insert an element into a sorted list *)
Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => [x]
  | cons h t => if Nat.leb x h then cons x l else cons h (insert x t)
  end.

(** Insertion sort *)
Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons h t => insert h (insertion_sort t)
  end.

(** Predicate for sorted lists *)
Fixpoint sorted (l : list nat) : bool :=
  match l with
  | nil => true
  | cons x rest => 
    match rest with
    | nil => true
    | cons y t => Nat.leb x y && sorted rest
    end
  end.

(** ** Basic Correctness Properties *)

(** Insert preserves length plus one *)
Theorem insert_length : forall x l,
  length (insert x l) = S (length l).
Proof.
  intros x l.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (Nat.leb x h).
    + simpl. reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

(** Insertion sort preserves length *)
Theorem insertion_sort_length : forall l,
  length (insertion_sort l) = length l.
Proof.
  intro l.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite insert_length. rewrite IH. reflexivity.
Qed. 