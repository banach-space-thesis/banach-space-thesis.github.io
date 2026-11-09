import BanachIsometric.LocalSignedIndex

/-!
# The canonical actual index as a signed-Jacobian integral

The proved almost-everywhere fiber count and signed area formula identify
every continuous target test supported in a sufficiently small ball with the
canonical actual integer index times its integral.
-/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped NNReal

theorem exists_localSignedIndex_integral_radius
    {n : ℕ} [NeZero n] {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0}
    (hf : LipschitzWith C f) (a b : PiolaSpace n) (hab : a ≤ b) (c : PiolaSpace n)
    (hc : c ∉ f '' piolaBoxBoundary a b) :
    ∃ r > 0, ∀ ψ : PiolaSpace n → ℝ, Continuous ψ → Function.support ψ ⊆ ball c r →
      (∫ x in Icc a b, (fderiv ℝ f x).det * ψ (f x)) =
        (localSignedIndex f a b c : ℝ) * ∫ y, ψ y := by
  obtain ⟨r, hr, hcount⟩ := localSignedIndex_spec hf a b hab c hc
  refine ⟨r, hr, ?_⟩
  intro ψ hψ hsupp
  rw [← integral_signedFiberCount_of_compact_lipschitz volume hf isCompact_Icc hψ]
  calc
    (∫ y, (signedFiberCount f (fderiv ℝ f) (Icc a b) y : ℝ) * ψ y) =
        ∫ y, (localSignedIndex f a b c : ℝ) * ψ y := by
      apply integral_congr_ae
      filter_upwards [hcount] with y hy
      by_cases hzero : ψ y = 0
      · simp only [hzero, mul_zero]
      · rw [hy (hsupp hzero)]
    _ = (localSignedIndex f a b c : ℝ) * ∫ y, ψ y := integral_const_mul _ _

end BanachIsometric
