import BanachIsometric.AELocallyConstant
import BanachIsometric.SignedCountLocalConstancy

/-! # Actual signed integer multiplicity on a preconnected target region -/

namespace BanachIsometric

open MeasureTheory Set
open scoped NNReal

theorem exists_signedFiberCount_ae_eq_on_preconnected
    {n : ℕ} [NeZero n] {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0}
    (hf : LipschitzWith C f) (a b : PiolaSpace n) (hab : a ≤ b)
    {U : Set (PiolaSpace n)} (hU : IsPreconnected U)
    (havoid : Disjoint U (f '' piolaBoxBoundary a b)) :
    ∃ D : ℤ, ∀ᵐ y, y ∈ U → signedFiberCount f (fderiv ℝ f) (Icc a b) y = D := by
  apply exists_ae_eq_const_on_of_ae_locally_constant volume hU
  intro x hx
  exact exists_signedFiberCount_ae_eq_on_ball hf a b hab x
    (fun himage => Set.disjoint_left.mp havoid hx himage)

end BanachIsometric
