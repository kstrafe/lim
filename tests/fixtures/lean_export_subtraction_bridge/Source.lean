namespace SubtractionBridgeSource

theorem successorCancellation (n m : Nat) :
    Nat.sub (Nat.succ n) (Nat.succ m) = Nat.sub n m :=
  Nat.succ_sub_succ_eq_sub n m

theorem doubleCancellation (n m : Nat) :
    Nat.sub (Nat.succ (Nat.succ n)) (Nat.succ (Nat.succ m)) = Nat.sub n m :=
  Eq.trans
    (Nat.succ_sub_succ_eq_sub (Nat.succ n) (Nat.succ m))
    (Nat.succ_sub_succ_eq_sub n m)

theorem mappedCancellation {A : Sort u} (f : A → Nat) (a b : A) :
    Nat.sub (Nat.succ (f a)) (Nat.succ (f b)) = Nat.sub (f a) (f b) :=
  Nat.succ_sub_succ_eq_sub (f a) (f b)

end SubtractionBridgeSource
