import BanachIsometric.SignedMultiplicityIntegrability
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Recovering the actual signed density from smooth target tests

The signed area formula and proved L¹ bound make distributional uniqueness
applicable to the actual integer fiber count. The target-test identities are
explicit hypotheses of this bridge, to be discharged by the analytic homotopy
argument. This bridge does not assume a pre-existing topological degree.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem ae_signedFiberCount_eq_of_test_integrals
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {C : ℝ≥0}
    (hf : LipschitzWith C f) {s : Set E} (hs : IsCompact s)
    {U : Set E} (hU : IsOpen U) (D : ℝ)
    (htests : ∀ test : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) test → HasCompactSupport test →
      tsupport test ⊆ U →
      (∫ x in s, (fderiv ℝ f x).det * test (f x) ∂μ) = D * ∫ y, test y ∂μ) :
    ∀ᵐ y ∂μ, y ∈ U → (signedFiberCount f (fderiv ℝ f) s y : ℝ) = D := by
  have hi := integrable_signedFiberCount_of_compact_lipschitz μ hf hs
  have hloc : LocallyIntegrableOn
      (fun y => (signedFiberCount f (fderiv ℝ f) s y : ℝ) - D) U μ :=
    (hi.locallyIntegrable.locallyIntegrableOn U).sub (locallyIntegrableOn_const D)
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · filter_upwards [hz] with y hy
    intro hyU
    exact sub_eq_zero.mp (hy hyU)
  · intro test htest hcompact hsub
    have hitest : Integrable test μ := htest.continuous.integrable_of_hasCompactSupport hcompact
    have hleft : Integrable
        (fun y => test y * (signedFiberCount f (fderiv ℝ f) s y : ℝ)) μ := by
      simpa only [mul_comm] using
        integrable_signedFiberCount_mul_of_compact_lipschitz μ hf hs htest.continuous
    have hright : Integrable (fun y => test y * D) μ := hitest.mul_const D
    have harea : (∫ y, test y * (signedFiberCount f (fderiv ℝ f) s y : ℝ) ∂μ) =
        ∫ x in s, (fderiv ℝ f x).det * test (f x) ∂μ := by
      simpa only [mul_comm] using integral_signedFiberCount_of_compact_lipschitz μ hf hs htest.continuous
    simp_rw [smul_eq_mul, mul_sub]
    rw [integral_sub hleft hright, harea, htests test htest hcompact hsub, integral_mul_const]
    ring

end BanachIsometric
