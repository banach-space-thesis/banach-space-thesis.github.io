import ThesisCommon.Analysis.IntegralKernelWeakCompact
import ThesisCommon.LpCut

/-! Quantitative cutoff bounds from the actual almost-everywhere range
bound. These are the elementary uniform-integrability estimates for the
bounded-kernel approximants. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ : Measure X} {ν : Measure Y}

theorem norm_lOneCut_eq_integral (B : Set Y) (hB : MeasurableSet B) (f : Lp ℝ 1 ν) :
    ‖lpCut B hB f‖ = ∫ y in B, ‖f y‖ ∂ν := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ y, ‖lpCut B hB f y‖ ∂ν) = ∫ y, B.indicator (fun z => ‖f z‖) y ∂ν := by
      apply integral_congr_ae
      filter_upwards [lpCut_coe B hB f] with y hy
      rw [hy]
      by_cases hyB : y ∈ B <;> simp [hyB]
    _ = _ := integral_indicator hB

theorem norm_lOneCut_comp_le_of_range_bound (T : E →L[ℝ] Lp ℝ 1 ν)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ f, ∀ᵐ y ∂ν, ‖T f y‖ ≤ C * ‖f‖)
    (B : Set Y) (hB : MeasurableSet B) (hνB : ν B < ∞) :
    ‖(lpCutL B hB).comp T‖ ≤ C * (ν B).toReal := by
  letI : IsFiniteMeasure (ν.restrict B) := ⟨by simpa using hνB⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC ENNReal.toReal_nonneg)
  intro f
  change ‖lpCut B hB (T f)‖ ≤ _
  rw [norm_lOneCut_eq_integral]
  calc
    (∫ y in B, ‖T f y‖ ∂ν) ≤ ∫ _ in B, C * ‖f‖ ∂ν :=
      integral_mono_ae (L1.integrable_coeFn _).norm.integrableOn
        (integrable_const _) (ae_restrict_of_ae (hbound f))
    _ = (C * (ν B).toReal) * ‖f‖ := by
      rw [integral_const]
      simp only [Measure.restrict_apply_univ, smul_eq_mul, measureReal_def]
      ring

theorem IsIntegralKernel.norm_cut_le_of_bound [SFinite μ] [IsFiniteMeasure ν]
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hk : IsIntegralKernel k K) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ z ∂μ.prod ν, ‖k z‖ ≤ C) (B : Set Y) (hB : MeasurableSet B) :
    ‖(lpCutL B hB).comp K‖ ≤ C * (ν B).toReal :=
  norm_lOneCut_comp_le_of_range_bound K hC (hk.apply_norm_le_of_bound hbound)
    B hB (measure_lt_top ν B)

end ThesisCommon
