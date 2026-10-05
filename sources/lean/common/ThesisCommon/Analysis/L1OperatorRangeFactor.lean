import ThesisCommon.Analysis.L1OperatorSigmaFiniteRange
import ThesisCommon.Analysis.LebesgueLpRestrictions
import ThesisCommon.Analysis.WeakEssentialNormProperties

/-! Actual restriction of an operator to a measurable output part containing
its range. Zero extension recovers the operator, and both the ordinary and
weak essential norms are unchanged. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem lebesgueLpExtend_restrict_of_supported (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (f : Lp 𝕜 1 ν) (hf : f =ᵐ[ν.restrict Θᶜ] 0) :
    lebesgueLpExtend (𝕜 := 𝕜) Θ hΘ (lebesgueLpRestrict (𝕜 := 𝕜) Θ f) = f := by
  apply Lp.ext
  have hr := (ae_restrict_iff' hΘ).mp (lebesgueLpRestrict_coe (𝕜 := 𝕜) Θ f)
  have hz := (ae_restrict_iff' hΘ.compl).mp hf
  filter_upwards [lebesgueLpExtend_coe (𝕜 := 𝕜) Θ hΘ (lebesgueLpRestrict (𝕜 := 𝕜) Θ f), hr, hz]
    with y he hr hz
  rw [he]
  by_cases hy : y ∈ Θ
  · simp [hy, hr hy]
  · simp [hy, hz hy]

theorem lOneOperator_restrict_range_factor
    (T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (hT : ∀ f, T f =ᵐ[ν.restrict Θᶜ] 0) :
    (lebesgueLpExtend (𝕜 := 𝕜) Θ hΘ).toContinuousLinearMap.comp
      ((lebesgueLpRestrict (𝕜 := 𝕜) Θ).comp T) = T := by
  apply ContinuousLinearMap.ext
  intro f
  exact lebesgueLpExtend_restrict_of_supported Θ hΘ (T f) (hT f)

theorem norm_lOneOperator_restrict_range
    (T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (hT : ∀ f, T f =ᵐ[ν.restrict Θᶜ] 0) :
    ‖(lebesgueLpRestrict (𝕜 := 𝕜) Θ).comp T‖ = ‖T‖ := by
  have h := congrArg norm (lOneOperator_restrict_range_factor T Θ hΘ hT)
  rw [LinearIsometry.norm_toContinuousLinearMap_comp] at h
  exact h

theorem weakEssentialNorm_lOneOperator_restrict_range
    (T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (hT : ∀ f, T f =ᵐ[ν.restrict Θᶜ] 0) :
    weakEssentialNorm ((lebesgueLpRestrict (𝕜 := 𝕜) Θ).comp T) = weakEssentialNorm T := by
  apply le_antisymm
  · exact (weakEssentialNorm_comp_left_le _ T).trans
      ((mul_le_mul_of_nonneg_right (norm_lebesgueLpRestrict_le (𝕜 := 𝕜) (E := 𝕜) (p := 1) (μ := ν) Θ)
        (weakEssentialNorm_nonneg T)).trans_eq (one_mul _))
  · conv_lhs => rw [← lOneOperator_restrict_range_factor T Θ hΘ hT]
    exact (weakEssentialNorm_comp_left_le _ _).trans
      ((mul_le_mul_of_nonneg_right ((lebesgueLpExtend (𝕜 := 𝕜) (E := 𝕜) (p := 1) (μ := ν) Θ hΘ).norm_toContinuousLinearMap_le)
        (weakEssentialNorm_nonneg _)).trans_eq (one_mul _))

theorem weaklyCompact_lOneOperator_restrict_range_iff
    (T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 ν) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (hT : ∀ f, T f =ᵐ[ν.restrict Θᶜ] 0) :
    IsWeaklyCompactOperator ((lebesgueLpRestrict (𝕜 := 𝕜) Θ).comp T) ↔ IsWeaklyCompactOperator T := by
  constructor
  · intro h
    rw [← lOneOperator_restrict_range_factor T Θ hΘ hT]
    exact h.comp_left _
  · exact fun h => h.comp_left _

theorem exists_sigmaFinite_lOneOperator_range_factor [IsFiniteMeasure μ]
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ∃ (Θ : Set Y) (hΘ : MeasurableSet Θ), SigmaFinite (ν.restrict Θ) ∧
      ∃ R : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (ν.restrict Θ),
        (lebesgueLpExtend (𝕜 := ℝ) Θ hΘ).toContinuousLinearMap.comp R = T ∧
        ‖R‖ = ‖T‖ ∧ weakEssentialNorm R = weakEssentialNorm T ∧
        (IsWeaklyCompactOperator R ↔ IsWeaklyCompactOperator T) := by
  obtain ⟨Θ, hΘ, hσ, hT⟩ := exists_sigmaFinite_range_part T
  exact ⟨Θ, hΘ, hσ, (lebesgueLpRestrict (𝕜 := ℝ) Θ).comp T,
    lOneOperator_restrict_range_factor T Θ hΘ hT,
    norm_lOneOperator_restrict_range T Θ hΘ hT,
    weakEssentialNorm_lOneOperator_restrict_range T Θ hΘ hT,
    weaklyCompact_lOneOperator_restrict_range_iff T Θ hΘ hT⟩

end ThesisCommon
