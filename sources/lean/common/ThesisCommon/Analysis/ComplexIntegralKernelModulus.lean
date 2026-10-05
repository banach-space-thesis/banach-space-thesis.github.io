import ThesisCommon.Analysis.ComplexIntegralKernelCoordinates
import ThesisCommon.Analysis.ComplexL1BandMembership
import ThesisCommon.Analysis.ComplexPhaseAE
import ThesisCommon.Analysis.IntegralOperatorBand
import ThesisCommon.Analysis.IntegralKernelSigmaFiniteBound

/-! The actual complex L1 operator modulus has the pointwise norm kernel.
The phase argument uses a countable dense family, so no uncountable
intersection of conull sets is assumed. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]
variable {k : X × Y → ℂ} {K : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν}

theorem IsIntegralKernel.phase (hk : IsIntegralKernel k K) (c : ℂ) :
    IsIntegralKernel (fun z => (c * k z).re) (complexL1OperatorPhase K c) := by
  have h := (hk.smul_rclike c).real_coordinate
  change IsIntegralKernel _ (complexL1OperatorRe (c • K)) at h
  simpa only [complexL1OperatorRe_smul, complexL1OperatorPhase] using h

theorem IsIntegralOperator.complex_modulus (hK : IsIntegralOperator K) :
    IsIntegralOperator (complexL1OperatorModulus K) := by
  apply (complexL1OperatorModulus_mem_iff integralOperatorOrderClosedIdeal K).mpr
  exact (isIntegralOperator_complex_coordinates_iff K).mp hK

theorem IsIntegralKernel.norm_le_modulus_kernel (hk : IsIntegralKernel k K)
    {m : X × Y → ℝ} (hm : IsIntegralKernel m (complexL1OperatorModulus K)) :
    ∀ᵐ z ∂μ.prod ν, ‖k z‖ ≤ m z := by
  apply complex_norm_le_of_phase_ae
  intro c hc
  apply ((hk.phase c).le_iff_kernel_le_sigmaFinite hm).mp
  exact (complexL1OperatorModulus_phase_isLUB K).1 ⟨c, hc, rfl⟩

/-- Integral domination on positive real inputs, with the genuine complex
operator and the genuine norm-kernel operator. -/
theorem IsIntegralKernel.complex_modulus_le_norm_kernel (hk : IsIntegralKernel k K)
    {H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hH : IsIntegralKernel (fun z => ‖k z‖) H) : complexL1OperatorModulus K ≤ H := by
  apply complexL1OperatorModulus_least
  intro f hf
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [hk.represents_real_input f, hk.integrable_real_input f,
    hH.represents f, complexL1Modulus_coe (K (complexL1OfReal μ f))] with y hkf hki hHf hmf
  rw [hmf, hkf, hHf]
  calc
    ‖∫ x, k (x,y) * (f x : ℂ) ∂μ‖ ≤ ∫ x, ‖k (x,y) * (f x : ℂ)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖k (x,y)‖ * f x ∂μ := by
      apply integral_congr_ae
      filter_upwards [(Lp.coeFn_nonneg f).mpr hf] with x hx
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx]

/-- The norm kernel is an actual integral kernel for the constructed modulus. -/
theorem IsIntegralKernel.complex_modulus (hk : IsIntegralKernel k K) :
    IsIntegralKernel (fun z => ‖k z‖) (complexL1OperatorModulus K) := by
  obtain ⟨m, hm⟩ := (show IsIntegralOperator K from ⟨k, hk⟩).complex_modulus
  have hkm := hk.norm_le_modulus_kernel hm
  have hb : HasKernelBound μ ν (fun z => ‖k z‖) ‖complexL1OperatorModulus K‖ := by
    apply hm.hasKernelBound_sigmaFinite.mono hk.measurable.norm
    filter_upwards [Measure.ae_ae_of_ae_prod hkm] with x hx
    filter_upwards [hx] with y hy
    simpa only [Real.norm_of_nonneg (norm_nonneg _), Real.norm_eq_abs] using
      hy.trans (le_abs_self (m (x,y)))
  let H := integralKernelOperator hk.measurable.norm hb
  have hH : IsIntegralKernel (fun z => ‖k z‖) H := isIntegralKernel_integralKernelOperator _ _
  have hHM : H ≤ complexL1OperatorModulus K :=
    (hH.le_iff_kernel_le_sigmaFinite hm).mpr hkm
  have heq := le_antisymm hHM (hk.complex_modulus_le_norm_kernel hH)
  rwa [heq] at hH

/-- Sharp column bound for complex kernels, derived from the operator norm. -/
theorem IsIntegralKernel.hasKernelBound_complex (hk : IsIntegralKernel k K) :
    HasKernelBound μ ν k ‖K‖ := by
  have hb := hk.complex_modulus.hasKernelBound_sigmaFinite
  rw [norm_complexL1OperatorModulus] at hb
  filter_upwards [hb] with x hx
  refine ⟨(integrable_norm_iff
    (hk.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mp hx.1, ?_⟩
  simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hx.2

end ThesisCommon
