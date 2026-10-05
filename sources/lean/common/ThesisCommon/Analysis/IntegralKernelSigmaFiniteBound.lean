import ThesisCommon.Analysis.IntegralKernelModulus
import ThesisCommon.Analysis.IntegralKernelDensity

/-! The sharp column bound extends to sigma-finite input measures by a
strictly positive finite change of measure. Zero input spaces are included. -/
noncomputable section
open MeasureTheory Filter
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem HasKernelBound.mono_const {k : X × Y → ℝ} {C D : ℝ}
    (hk : HasKernelBound μ ν k C) (hCD : C ≤ D) : HasKernelBound μ ν k D := by
  filter_upwards [hk] with x hx
  exact ⟨hx.1, hx.2.trans hCD⟩

theorem IsIntegralKernel.hasKernelBound_sigmaFinite [SigmaFinite μ] [SFinite ν]
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hk : IsIntegralKernel k K) : HasKernelBound μ ν k ‖K‖ := by
  obtain ⟨g, hg, hgpos, hgfin⟩ := exists_positive_finite_density μ
  letI := hgfin
  have hb := (hk.withDensity_input hg).hasKernelBound
  have hnorm : ‖K.comp (withDensitySMulLI μ (E := ℝ) hg).toContinuousLinearMap‖ ≤ ‖K‖ := by
    calc
      _ ≤ ‖K‖ * ‖(withDensitySMulLI μ (E := ℝ) hg).toContinuousLinearMap‖ := K.opNorm_comp_le _
      _ ≤ ‖K‖ * 1 := mul_le_mul_of_nonneg_left
        (withDensitySMulLI μ (E := ℝ) hg).norm_toContinuousLinearMap_le (norm_nonneg _)
      _ = ‖K‖ := mul_one _
  exact (ae_withDensity_coe_iff_of_pos hg hgpos).mp (hb.mono_const hnorm)

end ThesisCommon
