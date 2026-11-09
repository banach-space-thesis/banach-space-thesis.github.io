import ThesisCommon.Analysis.LpHaarBiorthogonal

/-! Identification of the first dyadic average with the constant Haar term. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical
namespace ThesisCommon

local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

theorem lpHaarRootCell_ae :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ lpHaarCell 0 0 := by
  simpa [lpHaarLevelCells_union, lpHaarCell, intervalLpDyadicRadius] using lpHaarLevelCells_cover 0

theorem lpHaarDyadicMean_root (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicMean 𝕜 p hp 0 f =
      lpHaarRawCoordinate 𝕜 p none f • lpHaarRawVector 𝕜 p none := by
  apply Lp.ext
  have hint : (∫ x in lpHaarCell 0 0, f x ∂(volume.restrict (Icc (0 : ℝ) 1))) =
      ∫ x, f x ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [Measure.restrict_eq_self_of_ae_mem lpHaarRootCell_ae]
  filter_upwards [lpHaarDyadicMean_coe 𝕜 p hp 0 f ⟨0, by simp⟩, lpHaarRootCell_ae,
    Lp.coeFn_smul (lpHaarRawCoordinate 𝕜 p none f) (lpHaarRawVector 𝕜 p none),
    Lp.coeFn_const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)] with x hav hx hsm hc
  rw [hsm]
  have hv : lpHaarRawVector 𝕜 p none x = 1 := hc
  simpa [lpHaarRawCoordinate, lpHaarRawVector, intervalLpDyadicRadius, hint, hv,
    Pi.smul_apply, smul_eq_mul] using hav hx

end ThesisCommon
