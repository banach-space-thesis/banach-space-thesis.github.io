import ThesisCommon.Analysis.SupportedWeakEssentialNorm
import ThesisCommon.Analysis.L1OperatorRangeFactor

/-! The support condition is equivalent to an actual operator into the
restricted L1 space, followed by zero extension. Weak compactness and the
distance definition agree with that literal source formulation. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [MeasurableSpace Y] {ν : Measure Y}

theorem l1OperatorSupportedOn_extend (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (V : E →L[𝕜] Lp 𝕜 1 (ν.restrict Θ)) :
    L1OperatorSupportedOn Θ ((lebesgueLpExtend (𝕜 := 𝕜) Θ hΘ).toContinuousLinearMap.comp V) := by
  intro f
  change ∀ᵐ y ∂ν.restrict Θᶜ, lebesgueLpExtend (𝕜 := 𝕜) Θ hΘ (V f) y = 0
  rw [ae_restrict_iff' hΘ.compl]
  filter_upwards [lebesgueLpExtend_coe (𝕜 := 𝕜) Θ hΘ (V f)] with y hy
  intro hyΘ
  simpa only [hy, indicator_of_notMem hyΘ] using (rfl : (0 : 𝕜) = 0)

theorem l1OperatorSupportedOn_iff_exists_restriction
    (Θ : Set Y) (hΘ : MeasurableSet Θ) (W : E →L[𝕜] Lp 𝕜 1 ν) :
    L1OperatorSupportedOn Θ W ↔ ∃ V : E →L[𝕜] Lp 𝕜 1 (ν.restrict Θ),
      (lebesgueLpExtend (𝕜 := 𝕜) Θ hΘ).toContinuousLinearMap.comp V = W := by
  constructor
  · intro hs
    refine ⟨(lebesgueLpRestrict (𝕜 := 𝕜) Θ).comp W, ?_⟩
    apply ContinuousLinearMap.ext
    intro f
    exact lebesgueLpExtend_restrict_of_supported Θ hΘ (W f) (hs f)
  · rintro ⟨V, rfl⟩
    exact l1OperatorSupportedOn_extend Θ hΘ V

theorem weaklyCompact_supported_iff_exists_restriction
    (Θ : Set Y) (hΘ : MeasurableSet Θ) (W : E →L[𝕜] Lp 𝕜 1 ν) :
    IsWeaklyCompactOperator W ∧ L1OperatorSupportedOn Θ W ↔
      ∃ V : E →L[𝕜] Lp 𝕜 1 (ν.restrict Θ), IsWeaklyCompactOperator V ∧
        (lebesgueLpExtend (𝕜 := 𝕜) Θ hΘ).toContinuousLinearMap.comp V = W := by
  constructor
  · rintro ⟨hW, hs⟩
    refine ⟨(lebesgueLpRestrict (𝕜 := 𝕜) Θ).comp W, hW.comp_left _, ?_⟩
    apply ContinuousLinearMap.ext
    intro f
    exact lebesgueLpExtend_restrict_of_supported Θ hΘ (W f) (hs f)
  · rintro ⟨V, hV, rfl⟩
    exact ⟨hV.comp_left _, l1OperatorSupportedOn_extend Θ hΘ V⟩

theorem supportedWeakEssentialNorm_eq_restrictionInf
    (Θ : Set Y) (hΘ : MeasurableSet Θ) (T : E →L[𝕜] Lp 𝕜 1 ν) :
    supportedWeakEssentialNorm Θ T = sInf {r : ℝ |
      ∃ V : E →L[𝕜] Lp 𝕜 1 (ν.restrict Θ), IsWeaklyCompactOperator V ∧
        r = ‖T - (lebesgueLpExtend (𝕜 := 𝕜) Θ hΘ).toContinuousLinearMap.comp V‖} := by
  unfold supportedWeakEssentialNorm
  congr 1
  ext r
  constructor
  · rintro ⟨W, hW, hs, rfl⟩
    obtain ⟨V, hV, heq⟩ := (weaklyCompact_supported_iff_exists_restriction Θ hΘ W).mp ⟨hW, hs⟩
    exact ⟨V, hV, by rw [heq]⟩
  · rintro ⟨V, hV, rfl⟩
    exact ⟨_, hV.comp_left _, l1OperatorSupportedOn_extend Θ hΘ V, rfl⟩

end ThesisCommon
