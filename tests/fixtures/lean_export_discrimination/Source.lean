namespace DiscriminationSource

theorem zeroNotSuccessor (n : Nat) (h : 0 = Nat.succ n) : False :=
  Nat.noConfusion h

theorem successorInjective (a b : Nat) (h : Nat.succ a = Nat.succ b) : a = b :=
  Nat.succ.inj h

theorem booleanDiscrimination (a b : Nat) (h : a = b) :
    (Nat.beq a b).rec False True :=
  noConfusion_of_Nat (fun x : Nat => x) h

theorem selfBooleanDiscrimination (n : Nat) :
    (Nat.beq n n).rec False True :=
  noConfusion_of_Nat (fun x : Nat => x) (Eq.refl n)

theorem mappedDiscrimination {A : Sort u} (f : A → Nat) (a b : A) (h : a = b) :
    (Nat.beq (f a) (f b)).rec False True :=
  noConfusion_of_Nat f h

end DiscriminationSource
