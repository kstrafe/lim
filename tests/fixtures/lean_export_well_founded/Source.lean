import Init.WF
namespace WellFoundedProbe
universe u v
theorem equation {A : Sort u} {motive : A → Sort v}
    (measure : A → Nat)
    (step : (x : A) → ((y : A) → measure y < measure x → motive y) → motive x)
    (x : A) :
    WellFounded.Nat.fix measure step x = step x (fun y _ => WellFounded.Nat.fix measure step y) :=
  WellFounded.Nat.fix_eq measure step x
end WellFoundedProbe
