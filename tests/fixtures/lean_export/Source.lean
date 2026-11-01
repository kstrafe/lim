/-
Copyright 2026 Lim contributors
SPDX-License-Identifier: Apache-2.0

Original small import fixtures. No upstream FLT proof text is used.
-/
universe u

namespace ReplaySource

def explicitIdentity (α : Sort u) (value : α) : α := value

theorem identityProof (proposition : Prop) (evidence : proposition) : proposition :=
  explicitIdentity proposition evidence

inductive NatLike where
  | zero
  | succ (predecessor : NatLike)

noncomputable def double (value : NatLike) : NatLike :=
  NatLike.rec
    (motive := fun _ => NatLike)
    NatLike.zero
    (fun _ doubledPredecessor => NatLike.succ (NatLike.succ doubledPredecessor))
    value

theorem doubleTwo :
    double (NatLike.succ (NatLike.succ NatLike.zero)) =
      NatLike.succ (NatLike.succ (NatLike.succ (NatLike.succ NatLike.zero))) := rfl

structure Package where
  number : Nat
  evidence : number = number

theorem projection : (Package.mk 2 rfl).number = 2 := rfl

mutual
  inductive Tree where
    | node (children : Forest)

  inductive Forest where
    | nil
    | cons (firstTree : Tree) (remainingTrees : Forest)
end

noncomputable def treeDepth (tree : Tree) : Nat :=
  @Tree.rec (fun _ => Nat) (fun _ => Nat)
    (fun _ childDepth => Nat.succ childDepth)
    Nat.zero
    (fun _ _ firstDepth remainingDepth => Nat.add firstDepth remainingDepth)
    tree

noncomputable def forestDepth (forest : Forest) : Nat :=
  @Forest.rec (fun _ => Nat) (fun _ => Nat)
    (fun _ childDepth => Nat.succ childDepth)
    Nat.zero
    (fun _ _ firstDepth remainingDepth => Nat.add firstDepth remainingDepth)
    forest

theorem mutualDepth :
    treeDepth (Tree.node (Forest.cons (Tree.node Forest.nil) Forest.nil)) = 2 := rfl

inductive Rose where
  | node (children : List Rose)

theorem nestedLeaf : Rose.node [] = Rose.node [] := rfl

end ReplaySource
