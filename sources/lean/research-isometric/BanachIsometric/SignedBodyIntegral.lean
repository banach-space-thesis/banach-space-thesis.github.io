import BanachIsometric.LipschitzSignedArea
import BanachIsometric.SignedCountExcision

/-!
# From the actual interior signed density to the body integral

A null boundary permits passage from the actual constant interior fiber count
to arbitrary continuous target weights. Outside the body, vanishing is derived
from the actual source image. No signed area identity is assumed here.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem integral_signedJacobian_eq_body_integral_of_interior_count
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {C : ℝ≥0}
    (hf : LipschitzWith C f) {S K : Set E} (hS : IsCompact S)
    (hK : MeasurableSet K) (hboundary : μ (frontier K) = 0)
    (himage : f '' S ⊆ K) (D : ℤ)
    (hcount : ∀ᵐ y ∂μ, y ∈ interior K → signedFiberCount f (fderiv ℝ f) S y = D)
    {ψ : E → ℝ} (hψ : Continuous ψ) :
    (∫ x in S, (fderiv ℝ f x).det * ψ (f x) ∂μ) = (D : ℝ) * ∫ y in K, ψ y ∂μ := by
  have hnot : ∀ᵐ y ∂μ, y ∉ frontier K := by
    apply ae_iff.mpr
    simpa only [not_not, Set.setOf_mem_eq] using hboundary
  rw [← integral_signedFiberCount_of_compact_lipschitz μ hf hS hψ]
  calc
    (∫ y, (signedFiberCount f (fderiv ℝ f) S y : ℝ) * ψ y ∂μ) =
        ∫ y, K.indicator (fun y => (D : ℝ) * ψ y) y ∂μ := by
      apply integral_congr_ae
      filter_upwards [hnot, hcount] with y hy hcy
      by_cases hyK : y ∈ K
      · have hyint : y ∈ interior K := by
          by_contra hni
          exact hy ⟨subset_closure hyK, hni⟩
        rw [indicator_of_mem hyK, hcy hyint]
      · have hnotImage : y ∉ f '' S := fun h => hyK (himage h)
        rw [signedFiberCount_eq_zero_of_not_mem_image f (fderiv ℝ f) S y hnotImage,
          Int.cast_zero, zero_mul, indicator_of_notMem hyK]
    _ = ∫ y in K, (D : ℝ) * ψ y ∂μ := integral_indicator hK
    _ = (D : ℝ) * ∫ y in K, ψ y ∂μ := integral_const_mul _ _

end BanachIsometric
