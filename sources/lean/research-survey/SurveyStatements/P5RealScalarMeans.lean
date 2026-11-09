import SurveyStatements.P5RealScalarMaps
import SurveyStatements.P5Cancellative

/-! Compatibility with both actual coordinate expectations, hence with the
actual doubly zero-mean subspace. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5.RealScalar

section RealIntegration
variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem integral_real_eq (f : Lp E p unitIntervalMeasure) :
    probabilityLpIntegral (𝕜 := 𝕜) f = probabilityLpIntegral (𝕜 := ℝ) f := by
  rw [probabilityLpIntegral_apply, probabilityLpIntegral_apply]
  change (@integral ℝ E _ (NormedSpace.restrictScalars ℝ 𝕜 E)
    _ unitIntervalMeasure (fun x => f x)) =
      (@integral ℝ E _ (NormedSpace.restrictScalars ℝ ℝ E)
        _ unitIntervalMeasure (fun x => f x))
  simp only [NormedSpace.restrictScalars_eq]

theorem mean_real_eq (f : Lp E p unitIntervalMeasure) :
    probabilityLpMean (𝕜 := 𝕜) f = probabilityLpMean (𝕜 := ℝ) f := by
  rw [probabilityLpMean_apply, probabilityLpMean_apply, integral_real_eq]

end RealIntegration

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem scalarEmbedding_mean (f : Lp ℝ p unitIntervalMeasure) :
    probabilityLpMean (𝕜 := 𝕜) (scalarEmbedding 𝕜 p f) =
      scalarEmbedding 𝕜 p (probabilityLpMean (𝕜 := ℝ) f) := by
  rw [mean_real_eq (𝕜 := 𝕜)]
  exact congrArg (fun L : Lp ℝ p unitIntervalMeasure →L[ℝ]
      Lp 𝕜 p unitIntervalMeasure => L f)
    (probabilityLpMean_natural (𝕜 := ℝ) (p := p) (μ := unitIntervalMeasure)
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜))

theorem scalarRetraction_mean (f : Lp 𝕜 p unitIntervalMeasure) :
    probabilityLpMean (𝕜 := ℝ) (scalarRetraction 𝕜 p f) =
      scalarRetraction 𝕜 p (probabilityLpMean (𝕜 := 𝕜) f) := by
  rw [mean_real_eq (𝕜 := 𝕜) f]
  exact congrArg (fun L : Lp 𝕜 p unitIntervalMeasure →L[ℝ]
      Lp ℝ p unitIntervalMeasure => L f)
    (probabilityLpMean_natural (𝕜 := ℝ) (p := p) (μ := unitIntervalMeasure)
      (RCLike.reCLM : 𝕜 →L[ℝ] ℝ))

theorem embedding_outerExpectation (f : MixedNorm ℝ p) :
    outerExpectation 𝕜 p (embedding 𝕜 p f) =
      embedding 𝕜 p (outerExpectation ℝ p f) := by
  change probabilityLpMean (𝕜 := 𝕜) (embedding 𝕜 p f) =
    embedding 𝕜 p (probabilityLpMean (𝕜 := ℝ) f)
  rw [mean_real_eq (𝕜 := 𝕜)]
  exact congrArg (fun L : MixedNorm ℝ p →L[ℝ] MixedNorm 𝕜 p => L f)
    (probabilityLpMean_natural (𝕜 := ℝ) (p := p) (μ := unitIntervalMeasure)
      (scalarEmbedding 𝕜 1))

theorem retraction_outerExpectation (f : MixedNorm 𝕜 p) :
    outerExpectation ℝ p (retraction 𝕜 p f) =
      retraction 𝕜 p (outerExpectation 𝕜 p f) := by
  change probabilityLpMean (𝕜 := ℝ) (retraction 𝕜 p f) =
    retraction 𝕜 p (probabilityLpMean (𝕜 := 𝕜) f)
  rw [mean_real_eq (𝕜 := 𝕜) f]
  exact congrArg (fun L : MixedNorm 𝕜 p →L[ℝ] MixedNorm ℝ p => L f)
    (probabilityLpMean_natural (𝕜 := ℝ) (p := p) (μ := unitIntervalMeasure)
      (scalarRetraction 𝕜 1))

theorem embedding_innerExpectation (f : MixedNorm ℝ p) :
    innerExpectation 𝕜 p (embedding 𝕜 p f) =
      embedding 𝕜 p (innerExpectation ℝ p f) := by
  apply Lp.ext
  filter_upwards [
    (probabilityLpMean (𝕜 := 𝕜) (E := 𝕜) (p := 1)
      (μ := unitIntervalMeasure)).coeFn_compLpL (embedding 𝕜 p f),
    (scalarEmbedding 𝕜 1).coeFn_compLpL f,
    (scalarEmbedding 𝕜 1).coeFn_compLpL (innerExpectation ℝ p f),
    (probabilityLpMean (𝕜 := ℝ) (E := ℝ) (p := 1)
      (μ := unitIntervalMeasure)).coeFn_compLpL f]
    with x hmean hmap hmapMean hrealMean
  change (embedding 𝕜 p f) x = scalarEmbedding 𝕜 1 (f x) at hmap
  change (innerExpectation ℝ p f) x = probabilityLpMean (𝕜 := ℝ) (f x) at hrealMean
  change (((probabilityLpMean (𝕜 := 𝕜) (E := 𝕜) (p := 1)
    (μ := unitIntervalMeasure)).compLpL p unitIntervalMeasure) (embedding 𝕜 p f)) x =
      ((scalarEmbedding 𝕜 1).compLpL p unitIntervalMeasure
        (innerExpectation ℝ p f)) x
  rw [hmean, hmap, hmapMean, hrealMean]
  exact scalarEmbedding_mean 𝕜 1 (f x)

theorem retraction_innerExpectation (f : MixedNorm 𝕜 p) :
    innerExpectation ℝ p (retraction 𝕜 p f) =
      retraction 𝕜 p (innerExpectation 𝕜 p f) := by
  apply Lp.ext
  filter_upwards [
    (probabilityLpMean (𝕜 := ℝ) (E := ℝ) (p := 1)
      (μ := unitIntervalMeasure)).coeFn_compLpL (retraction 𝕜 p f),
    (scalarRetraction 𝕜 1).coeFn_compLpL f,
    (scalarRetraction 𝕜 1).coeFn_compLpL (innerExpectation 𝕜 p f),
    (probabilityLpMean (𝕜 := 𝕜) (E := 𝕜) (p := 1)
      (μ := unitIntervalMeasure)).coeFn_compLpL f]
    with x hmean hmap hmapMean hscalarMean
  change (retraction 𝕜 p f) x = scalarRetraction 𝕜 1 (f x) at hmap
  change (innerExpectation 𝕜 p f) x = probabilityLpMean (𝕜 := 𝕜) (f x) at hscalarMean
  change (((probabilityLpMean (𝕜 := ℝ) (E := ℝ) (p := 1)
    (μ := unitIntervalMeasure)).compLpL p unitIntervalMeasure) (retraction 𝕜 p f)) x =
      ((scalarRetraction 𝕜 1).compLpL p unitIntervalMeasure
        (innerExpectation 𝕜 p f)) x
  rw [hmean, hmap, hmapMean, hscalarMean]
  exact scalarRetraction_mean 𝕜 1 (f x)

theorem embedding_mem_doublyZeroMean (f : MixedNorm ℝ p)
    (hf : f ∈ DoublyZeroMean ℝ p) : embedding 𝕜 p f ∈ DoublyZeroMean 𝕜 p := by
  constructor
  · change outerExpectation 𝕜 p (embedding 𝕜 p f) = 0
    have h : outerExpectation ℝ p f = 0 := hf.1
    rw [embedding_outerExpectation, h, map_zero]
  · change innerExpectation 𝕜 p (embedding 𝕜 p f) = 0
    have h : innerExpectation ℝ p f = 0 := hf.2
    rw [embedding_innerExpectation, h, map_zero]

theorem retraction_mem_doublyZeroMean (f : MixedNorm 𝕜 p)
    (hf : f ∈ DoublyZeroMean 𝕜 p) : retraction 𝕜 p f ∈ DoublyZeroMean ℝ p := by
  constructor
  · change outerExpectation ℝ p (retraction 𝕜 p f) = 0
    have h : outerExpectation 𝕜 p f = 0 := hf.1
    rw [retraction_outerExpectation, h, map_zero]
  · change innerExpectation ℝ p (retraction 𝕜 p f) = 0
    have h : innerExpectation 𝕜 p f = 0 := hf.2
    rw [retraction_innerExpectation, h, map_zero]

end SurveyStatements.P5.RealScalar
