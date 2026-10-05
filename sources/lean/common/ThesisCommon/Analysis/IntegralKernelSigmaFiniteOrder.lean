import ThesisCommon.Analysis.IntegralKernelOrder
import ThesisCommon.Analysis.IntegralKernelDensity

/-! Kernel order and uniqueness on sigma-finite input spaces, by the same
positive finite measure change used for the integral ideal. -/
noncomputable section
open MeasureTheory Filter
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SFinite ν]
variable {k h : X × Y → ℝ} {K H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

theorem IsIntegralKernel.nonneg_ae_of_positive_sigmaFinite (hk : IsIntegralKernel k K)
    (hK : ∀ f, 0 ≤ f → 0 ≤ K f) : ∀ᵐ z ∂μ.prod ν, 0 ≤ k z := by
  obtain ⟨g, hg, hgpos, hgfin⟩ := exists_positive_finite_density μ
  letI := hgfin
  have hpos := (hk.withDensity_input hg).nonneg_ae_of_positive
    (fun f hf => hK _ (withDensitySMulLI_nonneg hg f hf))
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const hk.measurable)).mpr
  exact (ae_withDensity_coe_iff_of_pos hg hgpos).mp (Measure.ae_ae_of_ae_prod hpos)

theorem IsIntegralKernel.positive_iff_nonneg_ae_sigmaFinite (hk : IsIntegralKernel k K) :
    (∀ f, 0 ≤ f → 0 ≤ K f) ↔ ∀ᵐ z ∂μ.prod ν, 0 ≤ k z :=
  ⟨hk.nonneg_ae_of_positive_sigmaFinite, hk.positive_of_nonneg_ae⟩

theorem IsIntegralKernel.le_iff_kernel_le_sigmaFinite
    (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h H) :
    (∀ f, 0 ≤ f → K f ≤ H f) ↔ k ≤ᵐ[μ.prod ν] h := by
  simpa only [ContinuousLinearMap.sub_apply, sub_nonneg] using
    (hh.sub hk).positive_iff_nonneg_ae_sigmaFinite

theorem IsIntegralKernel.kernel_unique_sigmaFinite
    (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h K) : k =ᵐ[μ.prod ν] h := by
  filter_upwards [(hk.le_iff_kernel_le_sigmaFinite hh).mp (fun _ _ => le_rfl),
    (hh.le_iff_kernel_le_sigmaFinite hk).mp (fun _ _ => le_rfl)] with z hz hz'
  exact le_antisymm hz hz'

end ThesisCommon
