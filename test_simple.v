(** Simple test to verify Coq compilation *)

(** Basic theorem *)
Theorem simple_test : forall P : Prop, P -> P.
Proof.
  intros P HP.
  exact HP.
Qed.

(** Test with natural numbers *)
Theorem zero_plus : forall n : nat, 0 + n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

(** Test computation *)
Compute 2 + 3.
Compute S (S 0). 