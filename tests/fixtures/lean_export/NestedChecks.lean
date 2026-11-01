/-
Copyright 2026 Lim contributors
SPDX-License-Identifier: Apache-2.0

Pinned producer acceptance/rejection checks for future nested replay support.
-/

inductive PositiveSigma where
  | leaf
  | node (pair : Sigma (fun (_ : Nat) => PositiveSigma))

/--
error: (kernel) invalid nested inductive datatype 'Eq', nested inductive datatypes parameters cannot contain local variables.
-/
#guard_msgs in
inductive RejectedEquality where
  | leaf
  | node (child : RejectedEquality) (evidence : child = child)

inductive RejectedConsumer (A : Type) where
  | make (consume : A -> Nat)

/--
error: (kernel) arg #1 of '_nested.RejectedConsumer_1.make' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive RejectedNegative where
  | node (consumer : RejectedConsumer RejectedNegative)
