import SurveyStatements.P5RealScalarMaps
import SurveyStatements.P5HaarBase

/-! The real embedding identifies the actual real and RCLike product-Haar
vectors. No basis or multiplier assertion is assumed here. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ENNReal

namespace SurveyStatements.P5.RealScalar

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem lifted_indicator (L : E →L[ℝ] F) (s : Set ℝ) (hs : MeasurableSet s) (c : E) :
    L.compLpL q unitIntervalMeasure (indicatorConstLp q hs (measure_ne_top _ _) c) =
      indicatorConstLp q hs (measure_ne_top _ _) (L c) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (indicatorConstLp q hs (measure_ne_top _ _) c),
    indicatorConstLp_coeFn (p := q) (hs := hs) (hμs := measure_ne_top unitIntervalMeasure s)
      (c := c),
    indicatorConstLp_coeFn (p := q) (hs := hs) (hμs := measure_ne_top unitIntervalMeasure s)
      (c := L c)] with x hL hc hLc
  rw [hL, hc, hLc]
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, indicator_of_mem hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, map_zero]

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem scalarEmbedding_dyadicHaar (I : DyadicIndex) :
    scalarEmbedding 𝕜 p (dyadicHaar ℝ p I) = dyadicHaar 𝕜 p I := by
  unfold dyadicHaar
  rw [map_sub]
  unfold scalarEmbedding
  rw [lifted_indicator, lifted_indicator]
  simp only [RCLike.ofRealCLM_apply, RCLike.ofReal_one]

theorem scalarRetraction_dyadicHaar (I : DyadicIndex) :
    scalarRetraction 𝕜 p (dyadicHaar 𝕜 p I) = dyadicHaar ℝ p I := by
  rw [← scalarEmbedding_dyadicHaar 𝕜 p I]
  exact congrArg (fun L : Lp ℝ p unitIntervalMeasure →L[ℝ]
      Lp ℝ p unitIntervalMeasure => L (dyadicHaar ℝ p I)) (scalar_retraction 𝕜 p)

theorem embedding_tensor (g : Lp ℝ 1 unitIntervalMeasure)
    (f : Lp ℝ p unitIntervalMeasure) :
    embedding 𝕜 p (tensorWith (𝕜 := ℝ) g f) =
      tensorWith (𝕜 := 𝕜) (scalarEmbedding 𝕜 1 g) (scalarEmbedding 𝕜 p f) := by
  apply Lp.ext
  filter_upwards [(scalarEmbedding 𝕜 1).coeFn_compLpL (tensorWith (𝕜 := ℝ) g f),
    tensorWith_ae (𝕜 := ℝ) g f,
    tensorWith_ae (𝕜 := 𝕜) (scalarEmbedding 𝕜 1 g) (scalarEmbedding 𝕜 p f),
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).coeFn_compLpL f]
    with x hE hrealTensor hscalarTensor hscalar
  change (scalarEmbedding 𝕜 p f) x = (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) (f x) at hscalar
  change ((scalarEmbedding 𝕜 1).compLpL p unitIntervalMeasure
    (tensorWith (𝕜 := ℝ) g f)) x =
      (tensorWith (𝕜 := 𝕜) (scalarEmbedding 𝕜 1 g) (scalarEmbedding 𝕜 p f)) x
  rw [hE, hrealTensor, hscalarTensor, hscalar, map_smul]
  exact RCLike.real_smul_eq_coe_smul (K := 𝕜) (f x) (scalarEmbedding 𝕜 1 g)

theorem embedding_productHaar (I J : DyadicIndex) :
    embedding 𝕜 p (productHaar ℝ p I J) = productHaar 𝕜 p I J := by
  unfold productHaar
  rw [embedding_tensor, scalarEmbedding_dyadicHaar 𝕜 1 J,
    scalarEmbedding_dyadicHaar 𝕜 p I]

theorem retraction_productHaar (I J : DyadicIndex) :
    retraction 𝕜 p (productHaar 𝕜 p I J) = productHaar ℝ p I J := by
  rw [← embedding_productHaar 𝕜 p I J]
  exact retraction_embedding_apply 𝕜 p _

end SurveyStatements.P5.RealScalar
