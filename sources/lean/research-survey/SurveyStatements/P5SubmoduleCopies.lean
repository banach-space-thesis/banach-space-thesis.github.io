import SurveyStatements.P5Averages

/-! Abstract lifting and restriction identities used by the concrete copies.
Keeping the maps abstract avoids unfolding their measure-space transports. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal

namespace SurveyStatements.P5

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lift_maps_into_kernel (L U : E →L[𝕜] E) (h : ∀ x, L (U x) = 0)
    (f : Lp E p unitIntervalMeasure) :
    L.compLpL p unitIntervalMeasure (U.compLpL p unitIntervalMeasure f) = 0 := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (U.compLpL p unitIntervalMeasure f),
    U.coeFn_compLpL f, Lp.coeFn_zero E p unitIntervalMeasure] with x hL hU hzero
  change (L.compLpL p unitIntervalMeasure (U.compLpL p unitIntervalMeasure f)) x =
    (0 : Lp E p unitIntervalMeasure) x
  rw [hL, hU, hzero]
  exact h (f x)

theorem lifted_map_preserves_zero_mean (U : E →L[𝕜] E)
    (f : Lp E p unitIntervalMeasure)
    (hf : probabilityLpMean (𝕜 := 𝕜) f = 0) :
    probabilityLpMean (𝕜 := 𝕜) (U.compLpL p unitIntervalMeasure f) = 0 := by
  have hc := congrArg (fun L : Lp E p unitIntervalMeasure →L[𝕜]
    Lp E p unitIntervalMeasure => L f) (probabilityLpMean_natural U)
  change probabilityLpMean (𝕜 := 𝕜) (U.compLpL p unitIntervalMeasure f) =
    U.compLpL p unitIntervalMeasure (probabilityLpMean (𝕜 := 𝕜) f) at hc
  rw [hc, hf, map_zero]

theorem codRestrict_retraction (S : Submodule 𝕜 F) (U : E →L[𝕜] F)
    (V : F →L[𝕜] E) (hU : ∀ x, U x ∈ S)
    (hVU : V.comp U = ContinuousLinearMap.id 𝕜 E) :
    (V.comp S.subtypeL).comp (U.codRestrict S hU) = ContinuousLinearMap.id 𝕜 E := by
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun L : E →L[𝕜] E => L x) hVU

theorem norm_codRestrict_le (S : Submodule 𝕜 F) (U : E →L[𝕜] F)
    (hU : ∀ x, U x ∈ S) : ‖U.codRestrict S hU‖ ≤ ‖U‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U)
  intro x
  exact U.le_opNorm x

theorem norm_comp_subtype_le (S : Submodule 𝕜 F) (V : F →L[𝕜] E) :
    ‖V.comp S.subtypeL‖ ≤ ‖V‖ := by
  calc
    _ ≤ ‖V‖ * ‖S.subtypeL‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖V‖ * 1 := mul_le_mul_of_nonneg_left (Submodule.norm_subtypeL_le S) (norm_nonneg V)
    _ = ‖V‖ := mul_one _

end SurveyStatements.P5
