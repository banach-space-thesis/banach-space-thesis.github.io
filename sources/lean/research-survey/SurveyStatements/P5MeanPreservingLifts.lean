import SurveyStatements.P5SubmoduleCopies
import SurveyStatements.P5Cancellative

/-! Integral-preserving maps on the inner L1 space preserve both genuine
zero-mean conditions after pointwise lifting to the mixed Bochner space. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem compLpL_comp (L U : E →L[𝕜] E) :
    (L.compLpL p unitIntervalMeasure).comp (U.compLpL p unitIntervalMeasure) =
      (L.comp U).compLpL p unitIntervalMeasure := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (U.compLpL p unitIntervalMeasure f),
    U.coeFn_compLpL f, (L.comp U).coeFn_compLpL f] with x hL hU hLU
  change (L.compLpL p unitIntervalMeasure (U.compLpL p unitIntervalMeasure f)) x =
    ((L.comp U).compLpL p unitIntervalMeasure f) x
  rw [hL, hU, hLU]
  rfl

theorem probabilityLpMean_comp_of_integral (U : Lp E p unitIntervalMeasure →L[𝕜]
    Lp E p unitIntervalMeasure)
    (hU : ∀ f, probabilityLpIntegral (𝕜 := 𝕜) (U f) =
      probabilityLpIntegral (𝕜 := 𝕜) f) :
    (probabilityLpMean (𝕜 := 𝕜) (E := E) (p := p)
      (μ := unitIntervalMeasure)).comp U = probabilityLpMean := by
  apply ContinuousLinearMap.ext
  intro f
  change Lp.const p unitIntervalMeasure (probabilityLpIntegral (𝕜 := 𝕜) (U f)) =
    Lp.const p unitIntervalMeasure (probabilityLpIntegral (𝕜 := 𝕜) f)
  rw [hU]

theorem innerExpectation_lift_of_integral
    (U : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (hU : ∀ f, probabilityLpIntegral (𝕜 := 𝕜) (U f) =
      probabilityLpIntegral (𝕜 := 𝕜) f) (f : MixedNorm 𝕜 p) :
    innerExpectation 𝕜 p (U.compLpL p unitIntervalMeasure f) =
      innerExpectation 𝕜 p f := by
  have he := compLpL_comp (p := p)
    (probabilityLpMean (𝕜 := 𝕜) (E := 𝕜) (p := 1)
      (μ := unitIntervalMeasure)) U
  rw [probabilityLpMean_comp_of_integral U hU] at he
  exact congrArg (fun L : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p => L f) he

theorem innerLift_mem_doublyZeroMean
    (U : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure)
    (hU : ∀ f, probabilityLpIntegral (𝕜 := 𝕜) (U f) =
      probabilityLpIntegral (𝕜 := 𝕜) f)
    (f : MixedNorm 𝕜 p) (hf : f ∈ DoublyZeroMean 𝕜 p) :
    U.compLpL p unitIntervalMeasure f ∈ DoublyZeroMean 𝕜 p := by
  constructor
  · exact lifted_map_preserves_zero_mean U f hf.1
  · change innerExpectation 𝕜 p (U.compLpL p unitIntervalMeasure f) = 0
    rw [innerExpectation_lift_of_integral U hU]
    exact hf.2

end SurveyStatements.P5
