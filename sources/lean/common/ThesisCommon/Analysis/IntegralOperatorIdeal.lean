import ThesisCommon.Analysis.IntegralOperatorMeasure
import ThesisCommon.Analysis.DominatedRadonNikodym
import ThesisCommon.Analysis.L1IndicatorExt
import ThesisCommon.Analysis.IntegralKernelLinear

/-! Positive ideal property of integral operators, for finite input measure
and sigma-finite output measure. The kernel is constructed by extending the
operator content and taking its Radon--Nikodym density. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SigmaFinite ν]
variable {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

set_option maxHeartbeats 800000 in
/-- The finite-measure version of the positive ideal theorem, with the
actual dominated kernel retained in the conclusion. -/
theorem IsIntegralKernel.exists_kernel_of_positive_le (hk : IsIntegralKernel k K)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) :
    ∃ r : X × Y → ℝ, IsIntegralKernel r S ∧ (∀ z, 0 ≤ r z) ∧ r ≤ᵐ[μ.prod ν] k := by
  have hK : ∀ f, 0 ≤ f → 0 ≤ K f := fun f hf => (hS f hf).trans (hSK f hf)
  let M := dominatedOperatorMeasure hk S hS hSK
  obtain ⟨r, hrm, hrpos, hri, hrle, hrM⟩ := exists_density_of_le_withDensity M (μ.prod ν)
    hk.integrable (hk.nonneg_ae_of_positive hK)
    (dominatedOperatorMeasure_le_kernelMeasure hk S hS hSK)
  have hnorm : ∀ᵐ z ∂μ.prod ν, ‖r z‖ ≤ ‖k z‖ := hrle.mono fun z hz => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hrpos z)] using hz.trans (le_abs_self (k z))
  have hbound : HasKernelBound μ ν r ‖K‖ :=
    hk.hasKernelBound.mono hrm (Measure.ae_ae_of_ae_prod hnorm)
  let H := integralKernelOperator hrm hbound
  have hrH : IsIntegralKernel r H := isIntegralKernel_integralKernelOperator hrm hbound
  have hH : ∀ f, 0 ≤ f → 0 ≤ H f := hrH.positive_of_nonneg_ae (Eventually.of_forall hrpos)
  have heq : S = H := by
    apply lOne_continuousLinearMap_ext_indicators
    intro a ha
    apply Lp.ext
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L1.integrable_coeFn _) (L1.integrable_coeFn _)
    intro b hb _
    have he : ENNReal.ofReal (∫ y in b, S (lOneIndicator μ a ha) y ∂ν) =
        ENNReal.ofReal (∫ y in b, H (lOneIndicator μ a ha) y ∂ν) := by
      rw [← dominatedOperatorMeasure_prod hk S hS hSK ha hb,
        ← operatorSetIntegral_prod H ha hb]
      change M (a ×ˢ b) = operatorContent H hH (a ×ˢ b)
      rw [hrH.operatorContent_eq_kernelMeasure hH (prod_mem_finiteSectionAlgebra ha hb)]
      exact congrArg (fun m : Measure (X × Y) => m (a ×ˢ b)) hrM.symm
    have hSpos : 0 ≤ ∫ y in b, S (lOneIndicator μ a ha) y ∂ν := integral_nonneg_of_ae (ae_restrict_of_ae
      ((Lp.coeFn_nonneg _).mpr (hS _ (lOneIndicator_nonneg a ha))))
    have hHpos : 0 ≤ ∫ y in b, H (lOneIndicator μ a ha) y ∂ν := integral_nonneg_of_ae (ae_restrict_of_ae
      ((Lp.coeFn_nonneg _).mpr (hH _ (lOneIndicator_nonneg a ha))))
    have he' := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_ofReal hSpos, ENNReal.toReal_ofReal hHpos] using he'
  exact ⟨r, heq.symm ▸ hrH, hrpos, hrle⟩

theorem IsIntegralOperator.of_positive_le {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hK : IsIntegralOperator K) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) : IsIntegralOperator S := by
  obtain ⟨k, hk⟩ := hK
  obtain ⟨r, hr, _, _⟩ := hk.exists_kernel_of_positive_le S hS hSK
  exact ⟨r, hr⟩

/-- Domination of the absolute output on positive inputs also gives a
kernel for a signed operator. Apply the positive result to K-S <= 2K. -/
theorem IsIntegralOperator.of_abs_apply_le {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hK : IsIntegralOperator K) (hSK : ∀ f, 0 ≤ f → |S f| ≤ K f) :
    IsIntegralOperator S := by
  have hR : IsIntegralOperator (K - S) := (hK.smul 2).of_positive_le
    (fun f hf => sub_nonneg.mpr ((le_abs_self _).trans (hSK f hf))) (by
      intro f hf
      change K f - S f ≤ (2 : ℝ) • K f
      rw [two_smul, sub_eq_add_neg]
      exact add_le_add_left ((neg_le_abs _).trans (hSK f hf)) _)
  simpa only [sub_sub_cancel] using hK.sub hR

/-- Solidity with respect to the constructed operator modulus. -/
theorem IsIntegralOperator.of_modulus_le {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hK : IsIntegralOperator K)
    (hSK : ∀ f, 0 ≤ f → lOneOperatorModulus S f ≤ lOneOperatorModulus K f) :
    IsIntegralOperator S := by
  obtain ⟨k, hk⟩ := hK
  apply IsIntegralOperator.of_abs_apply_le (K := lOneOperatorModulus K) ⟨_, hk.modulus⟩
  intro f hf
  have h := lOneOperatorModulus_dominates S f
  rw [abs_of_nonneg hf] at h
  exact h.trans (hSK f hf)

end ThesisCommon
