import Init.Core
namespace BasisProbe
noncomputable def pick : Nat := Classical.choice (Nonempty.intro 0)
theorem choiceReflexive : pick = pick := rfl
theorem propositionEquality (P Q : Prop) (forward : P -> Q) (backward : Q -> P) : P = Q :=
  propext (Iff.intro forward backward)
theorem quotientRelated (a b : Nat) :
    Quot.mk (fun (_ _ : Nat) => True) a = Quot.mk (fun (_ _ : Nat) => True) b :=
  Quot.sound True.intro
end BasisProbe
