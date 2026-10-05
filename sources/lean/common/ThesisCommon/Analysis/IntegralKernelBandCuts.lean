import ThesisCommon.Analysis.L1AdjointOneKernel
import ThesisCommon.Analysis.L1AdjointOneBands

/-! Output band cuts of actual kernels, including their adjoint-one densities. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem IsIntegralKernel.outputCut {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hk : IsIntegralKernel k K) (B : Set Y) (hB : MeasurableSet B) :
    IsIntegralKernel ((univ ×ˢ B).indicator k) ((lpCutL B hB).comp K) where
  measurable := hk.measurable.indicator (MeasurableSet.univ.prod hB)
  integrable_section f := by
    filter_upwards [hk.integrable_section f] with y hy
    by_cases hyB : y ∈ B
    · simpa only [mem_prod, mem_univ, true_and, hyB, indicator_of_mem] using hy
    · simp only [mem_prod, mem_univ, true_and, hyB, not_false_eq_true, indicator_of_notMem,
        zero_mul, integrable_zero]
  represents f := by
    filter_upwards [hk.represents f, lpCut_coe B hB (K f)] with y hy hcut
    change lpCut B hB (K f) y = _
    rw [hcut]
    by_cases hyB : y ∈ B
    · simpa only [indicator_of_mem hyB, mem_prod, mem_univ, true_and, hyB, indicator_of_mem] using hy
    · simp only [indicator_of_notMem hyB, mem_prod, mem_univ, true_and, hyB,
        not_false_eq_true, indicator_of_notMem, zero_mul, integral_zero]

theorem IsIntegralKernel.positiveAdjointOneDensity_outputCut [IsFiniteMeasure μ] [SFinite ν]
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hk : IsIntegralKernel k K) (hK : 0 ≤ K) (B : Set Y) (hB : MeasurableSet B) :
    positiveAdjointOneDensity ((lpCutL B hB).comp K) (positive_outputCut_nonneg hK B hB)
      =ᵐ[μ] fun x => ∫ y in B, k (x, y) ∂ν := by
  have heq := (hk.outputCut B hB).positiveAdjointOne_eq_column_ae (positive_outputCut_nonneg hK B hB)
  filter_upwards [heq, positiveAdjointOne_coe ((lpCutL B hB).comp K)
    (positive_outputCut_nonneg hK B hB)] with x hx hcoe
  rw [← hcoe, hx, ← integral_indicator hB]
  congr 1
  funext y
  by_cases hy : y ∈ B <;> simp [hy]

end ThesisCommon
