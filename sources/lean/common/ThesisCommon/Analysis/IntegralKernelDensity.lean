import ThesisCommon.Analysis.IntegralKernel
import ThesisCommon.Analysis.L1DensityEquiv

/-! Changing the input measure by a positive weight preserves the same
kernel when the input L1 isometry multiplies by that weight. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} {g : X → ℝ≥0}
variable {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

omit [MeasurableSpace Y] in
theorem integrable_withDensity_kernel_iff (hg : Measurable g)
    (k : X × Y → ℝ) (f : Lp ℝ 1 (μ.withDensity (fun x => (g x : ℝ≥0∞)))) (y : Y) :
    Integrable (fun x => k (x, y) * f x) (μ.withDensity (fun x => (g x : ℝ≥0∞))) ↔
      Integrable (fun x => k (x, y) * withDensitySMulLI μ hg f x) μ := by
  rw [integrable_withDensity_iff_integrable_coe_smul hg]
  apply integrable_congr
  filter_upwards [withDensitySMulLI_coe hg f] with x hx
  rw [hx, smul_eq_mul]
  ring

omit [MeasurableSpace Y] in
theorem integral_withDensity_kernel (hg : Measurable g)
    (k : X × Y → ℝ) (f : Lp ℝ 1 (μ.withDensity (fun x => (g x : ℝ≥0∞)))) (y : Y) :
    (∫ x, k (x, y) * f x ∂μ.withDensity (fun x => (g x : ℝ≥0∞))) =
      ∫ x, k (x, y) * withDensitySMulLI μ hg f x ∂μ := by
  rw [integral_withDensity_eq_integral_smul hg]
  apply integral_congr_ae
  filter_upwards [withDensitySMulLI_coe hg f] with x hx
  rw [hx, NNReal.smul_def, smul_eq_mul]
  ring

theorem IsIntegralKernel.withDensity_input (hk : IsIntegralKernel k K) (hg : Measurable g) :
    IsIntegralKernel k (K.comp (withDensitySMulLI μ hg).toContinuousLinearMap) where
  measurable := hk.measurable
  integrable_section f := (hk.integrable_section (withDensitySMulLI μ hg f)).mono fun y hy =>
    (integrable_withDensity_kernel_iff hg k f y).mpr hy
  represents f := by
    filter_upwards [hk.represents (withDensitySMulLI μ hg f)] with y hy
    exact hy.trans (integral_withDensity_kernel hg k f y).symm

theorem IsIntegralKernel.of_withDensity_input (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x)
    (hk : IsIntegralKernel k (K.comp (withDensitySMulLI μ hg).toContinuousLinearMap)) :
    IsIntegralKernel k K where
  measurable := hk.measurable
  integrable_section f := by
    obtain ⟨v, rfl⟩ := withDensitySMulLI_surjective hg hpos f
    exact (hk.integrable_section v).mono fun y hy => (integrable_withDensity_kernel_iff hg k v y).mp hy
  represents f := by
    obtain ⟨v, rfl⟩ := withDensitySMulLI_surjective hg hpos f
    filter_upwards [hk.represents v] with y hy
    exact hy.trans (integral_withDensity_kernel hg k v y)

end ThesisCommon
