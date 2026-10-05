import ThesisCommon.Analysis.L1OperatorRangeFactor
import ThesisCommon.Analysis.ComplexL1OperatorModulus
import ThesisCommon.Analysis.L1DensityEquivRCLike

/-! Complex L1 operators with finite or sigma-finite input have a common
sigma-finite measurable output support, even for arbitrary output measure. -/
noncomputable section
open MeasureTheory Filter
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem exists_sigmaFinite_range_part_complex [IsFiniteMeasure μ]
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    ∃ Θ : Set Y, MeasurableSet Θ ∧ SigmaFinite (ν.restrict Θ) ∧
      ∀ f, T f =ᵐ[ν.restrict Θᶜ] 0 := by
  obtain ⟨Θ, hΘ, hσ, hM⟩ := exists_sigmaFinite_range_part (complexL1OperatorModulus T)
  refine ⟨Θ, hΘ, hσ, fun f => ?_⟩
  have hdom := ae_restrict_of_ae (s := Θᶜ)
    ((Lp.coeFn_le _ _).mpr (complexL1OperatorModulus_dominates T f))
  filter_upwards [hdom, ae_restrict_of_ae (complexL1Modulus_coe (T f)),
    hM (complexL1Modulus f)] with y hd hm hz
  change T f y = 0
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hm, hz, Pi.zero_apply] using hd

theorem exists_sigmaFinite_range_part_complex_sigmaFinite [SigmaFinite μ]
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    ∃ Θ : Set Y, MeasurableSet Θ ∧ SigmaFinite (ν.restrict Θ) ∧
      ∀ f, T f =ᵐ[ν.restrict Θᶜ] 0 := by
  obtain ⟨g, hg, hpos, hfin⟩ := exists_positive_finite_density μ
  letI := hfin
  let e := lOneWithDensityEquiv_rclike (𝕜 := ℂ) hg hpos
  obtain ⟨Θ, hΘ, hσ, hT⟩ := exists_sigmaFinite_range_part_complex
    (T.comp e.toLinearIsometry.toContinuousLinearMap)
  refine ⟨Θ, hΘ, hσ, fun f => ?_⟩
  have h := hT (e.symm f)
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply] using h

theorem exists_sigmaFinite_complex_lOneOperator_range_factor [SigmaFinite μ]
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    ∃ (Θ : Set Y) (hΘ : MeasurableSet Θ), SigmaFinite (ν.restrict Θ) ∧
      ∃ R : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 (ν.restrict Θ),
        (lebesgueLpExtend (𝕜 := ℂ) Θ hΘ).toContinuousLinearMap.comp R = T ∧
        ‖R‖ = ‖T‖ ∧ weakEssentialNorm R = weakEssentialNorm T ∧
        (IsWeaklyCompactOperator R ↔ IsWeaklyCompactOperator T) := by
  obtain ⟨Θ, hΘ, hσ, hT⟩ := exists_sigmaFinite_range_part_complex_sigmaFinite T
  exact ⟨Θ, hΘ, hσ, (lebesgueLpRestrict (𝕜 := ℂ) Θ).comp T,
    lOneOperator_restrict_range_factor T Θ hΘ hT,
    norm_lOneOperator_restrict_range T Θ hΘ hT,
    weakEssentialNorm_lOneOperator_restrict_range T Θ hΘ hT,
    weaklyCompact_lOneOperator_restrict_range_iff T Θ hΘ hT⟩

end ThesisCommon
