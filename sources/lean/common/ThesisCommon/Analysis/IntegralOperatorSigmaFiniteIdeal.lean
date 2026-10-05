import ThesisCommon.Analysis.IntegralOperatorIdeal
import ThesisCommon.Analysis.IntegralKernelDensity

/-! The real integral ideal on sigma-finite L1 spaces. Change the input to
an equivalent finite measure, apply the proved finite-input ideal, and
transport the actual kernel back through the weighted L1 isometry. -/
noncomputable section
open MeasureTheory Filter
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]
variable {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

theorem IsIntegralKernel.exists_kernel_of_positive_le_sigmaFinite (hk : IsIntegralKernel k K)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) :
    ∃ r : X × Y → ℝ, IsIntegralKernel r S ∧ (∀ z, 0 ≤ r z) ∧ r ≤ᵐ[μ.prod ν] k := by
  obtain ⟨g, hg, hgpos, hgfin⟩ := exists_positive_finite_density μ
  letI := hgfin
  let A := (withDensitySMulLI μ (E := ℝ) hg).toContinuousLinearMap
  obtain ⟨r, hr, hrpos, hrle⟩ := (hk.withDensity_input hg).exists_kernel_of_positive_le (S.comp A)
    (fun f hf => hS _ (withDensitySMulLI_nonneg hg f hf))
    (fun f hf => hSK _ (withDensitySMulLI_nonneg hg f hf))
  refine ⟨r, hr.of_withDensity_input hg hgpos, hrpos, ?_⟩
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hr.measurable hk.measurable)).mpr
  exact (ae_withDensity_coe_iff_of_pos hg hgpos).mp (Measure.ae_ae_of_ae_prod hrle)

theorem IsIntegralOperator.of_positive_le_sigmaFinite {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hK : IsIntegralOperator K) (hS : ∀ f, 0 ≤ f → 0 ≤ S f)
    (hSK : ∀ f, 0 ≤ f → S f ≤ K f) : IsIntegralOperator S := by
  obtain ⟨k, hk⟩ := hK
  obtain ⟨r, hr, _, _⟩ := hk.exists_kernel_of_positive_le_sigmaFinite S hS hSK
  exact ⟨r, hr⟩

theorem IsIntegralOperator.of_abs_apply_le_sigmaFinite {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hK : IsIntegralOperator K) (hSK : ∀ f, 0 ≤ f → |S f| ≤ K f) :
    IsIntegralOperator S := by
  have hR : IsIntegralOperator (K - S) := (hK.smul 2).of_positive_le_sigmaFinite
    (fun f hf => sub_nonneg.mpr ((le_abs_self _).trans (hSK f hf))) (by
      intro f hf
      change K f - S f ≤ (2 : ℝ) • K f
      rw [two_smul, sub_eq_add_neg]
      exact add_le_add_left ((neg_le_abs _).trans (hSK f hf)) _)
  simpa only [sub_sub_cancel] using hK.sub hR

theorem IsIntegralOperator.of_modulus_le_sigmaFinite {S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hK : IsIntegralOperator K)
    (hSK : ∀ f, 0 ≤ f → lOneOperatorModulus S f ≤ lOneOperatorModulus K f) :
    IsIntegralOperator S := by
  obtain ⟨k, hk⟩ := hK
  apply IsIntegralOperator.of_abs_apply_le_sigmaFinite (K := lOneOperatorModulus K) ⟨_, hk.modulus⟩
  intro f hf
  have h := lOneOperatorModulus_dominates S f
  rw [abs_of_nonneg hf] at h
  exact h.trans (hSK f hf)

end ThesisCommon
