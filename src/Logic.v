(** * Logical Foundations *)

(** This file explores fundamental logical concepts in Coq,
    including propositions, logical connectives, and quantifiers. *)

(** ** Conjunction (AND) *)

(** Conjunction introduction *)
Theorem and_intro : forall P Q : Prop,
  P -> Q -> P /\ Q.
Proof.
  intros P Q HP HQ.
  split.
  - exact HP.
  - exact HQ.
Qed.

(** Conjunction elimination *)
Theorem and_elim_l : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  exact HP.
Qed.

Theorem and_elim_r : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  exact HQ.
Qed.

(** Conjunction is commutative *)
Theorem and_comm : forall P Q : Prop,
  P /\ Q <-> Q /\ P.
Proof.
  intros P Q.
  split.
  - intro H.
    destruct H as [HP HQ].
    split; [exact HQ | exact HP].
  - intro H.
    destruct H as [HQ HP].
    split; [exact HP | exact HQ].
Qed.

(** ** Disjunction (OR) *)

(** Disjunction is commutative *)
Theorem or_comm : forall P Q : Prop,
  P \/ Q <-> Q \/ P.
Proof.
  intros P Q.
  split.
  - intro H.
    destruct H as [HP | HQ].
    + right. exact HP.
    + left. exact HQ.
  - intro H.
    destruct H as [HQ | HP].
    + right. exact HQ.
    + left. exact HP.
Qed.

(** ** Implication *)

(** Implication is transitive *)
Theorem impl_trans : forall P Q R : Prop,
  (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R HPQ HQR HP.
  apply HQR.
  apply HPQ.
  exact HP.
Qed.

(** ** Negation *)

(** Double negation introduction *)
Theorem double_neg_intro : forall P : Prop,
  P -> ~~P.
Proof.
  intros P HP HnotP.
  apply HnotP.
  exact HP.
Qed.

(** Contraposition *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ HnotQ HP.
  apply HnotQ.
  apply HPQ.
  exact HP.
Qed.

(** ** De Morgan's Laws *)

(** De Morgan's law for conjunction (constructive version) *)
Theorem de_morgan_and_partial : forall P Q : Prop,
  (~P \/ ~Q) -> ~(P /\ Q).
Proof.
  intros P Q H HPQ.
  destruct H as [HnotP | HnotQ].
  - destruct HPQ as [HP HQ].
    apply HnotP. exact HP.
  - destruct HPQ as [HP HQ].
    apply HnotQ. exact HQ.
Qed.

(** ** Quantifiers *)

(** Properties involving universal quantification *)
Theorem forall_and_dist : forall (A : Type) (P Q : A -> Prop),
  (forall x : A, P x /\ Q x) <-> 
  (forall x : A, P x) /\ (forall x : A, Q x).
Proof.
  intros A P Q.
  split.
  - intro H.
    split.
    + intro x. destruct (H x) as [HPx HQx]. exact HPx.
    + intro x. destruct (H x) as [HPx HQx]. exact HQx.
  - intro H.
    destruct H as [HforallP HforallQ].
    intro x.
    split.
    + apply HforallP.
    + apply HforallQ.
Qed.

(** Existential quantification distributes over disjunction *)
Theorem exists_or_dist : forall (A : Type) (P Q : A -> Prop),
  (exists x : A, P x \/ Q x) <-> 
  (exists x : A, P x) \/ (exists x : A, Q x).
Proof.
  intros A P Q.
  split.
  - intro H.
    destruct H as [x [HPx | HQx]].
    + left. exists x. exact HPx.
    + right. exists x. exact HQx.
  - intro H.
    destruct H as [[x HPx] | [x HQx]].
    + exists x. left. exact HPx.
    + exists x. right. exact HQx.
Qed. 