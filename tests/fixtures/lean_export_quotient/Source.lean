/- Original constructive fixture for pinned quotient computation replay.
   No axioms, admissions, native_decide, choice, propext, or Quot.sound. -/
namespace QuotientSource

def eqRel (a b : Nat) : Prop := Eq a b

def liftIdentity : Quot eqRel -> Nat :=
  @Quot.lift Nat eqRel Nat (fun a => a) (fun _ _ h => h)

theorem liftComputes : liftIdentity (Quot.mk eqRel 3) = 3 := rfl

def liftFunction : Quot eqRel -> (Nat -> Nat) :=
  @Quot.lift Nat eqRel (Nat -> Nat) (fun _ y => y) (fun _ _ _ => rfl)

theorem extraArgumentComputes : liftFunction (Quot.mk eqRel 3) 4 = 4 := rfl

theorem inductionReflexive (q : Quot eqRel) : liftIdentity q = liftIdentity q :=
  @Quot.ind Nat eqRel (fun x => liftIdentity x = liftIdentity x)
    (fun _ => rfl) q

end QuotientSource
