import SurveyStatements.P5Cancellative

/-! Genuine elementary tensors and the zero-mean tensor inclusion from the
paper's cancellative-projection lemma. No Haar density assertion is assumed. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal

namespace SurveyStatements.P5

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For a fixed inner L1 vector `g`, send `x(s)` to `x(s) • g`. -/
def tensorWith (g : Lp 𝕜 1 unitIntervalMeasure) :
    Lp 𝕜 p unitIntervalMeasure →L[𝕜] MixedNorm 𝕜 p :=
  ((ContinuousLinearMap.id 𝕜 𝕜).smulRight g).compLpL p unitIntervalMeasure

theorem tensorWith_ae (g : Lp 𝕜 1 unitIntervalMeasure)
    (x : Lp 𝕜 p unitIntervalMeasure) :
    tensorWith g x =ᵐ[unitIntervalMeasure] fun s => x s • g :=
  ((ContinuousLinearMap.id 𝕜 𝕜).smulRight g).coeFn_compLpL x

theorem outerExpectation_tensor (g : Lp 𝕜 1 unitIntervalMeasure)
    (x : Lp 𝕜 p unitIntervalMeasure) :
    outerExpectation 𝕜 p (tensorWith g x) =
      tensorWith g (probabilityLpMean (𝕜 := 𝕜) x) :=
  congrArg (fun L => L x)
    (probabilityLpMean_natural ((ContinuousLinearMap.id 𝕜 𝕜).smulRight g))

theorem innerExpectation_tensor (g : Lp 𝕜 1 unitIntervalMeasure)
    (x : Lp 𝕜 p unitIntervalMeasure) :
    innerExpectation 𝕜 p (tensorWith g x) =
      tensorWith (probabilityLpMean (𝕜 := 𝕜) g) x := by
  apply Lp.ext
  filter_upwards [
    (probabilityLpMean (𝕜 := 𝕜) (E := 𝕜) (p := 1) (μ := unitIntervalMeasure)).coeFn_compLpL
      (tensorWith g x), tensorWith_ae g x,
    tensorWith_ae (probabilityLpMean (𝕜 := 𝕜) g) x] with s hinner hleft hright
  change (innerExpectation 𝕜 p (tensorWith g x)) s =
    (tensorWith (probabilityLpMean (𝕜 := 𝕜) g) x) s
  unfold innerExpectation
  rw [hinner, hleft, hright, map_smul]

/-- An outer mean-zero vector tensor an inner mean-zero vector lies in the
actual intersection of the two expectation kernels. -/
theorem tensor_mem_doublyZeroMean (g : Lp 𝕜 1 unitIntervalMeasure)
    (x : Lp 𝕜 p unitIntervalMeasure)
    (hg : probabilityLpMean (𝕜 := 𝕜) g = 0)
    (hx : probabilityLpMean (𝕜 := 𝕜) x = 0) :
    tensorWith g x ∈ DoublyZeroMean 𝕜 p := by
  constructor
  · change outerExpectation 𝕜 p (tensorWith g x) = 0
    rw [outerExpectation_tensor, hx, map_zero]
  · change innerExpectation 𝕜 p (tensorWith g x) = 0
    rw [innerExpectation_tensor, hg]
    apply Lp.ext
    filter_upwards [tensorWith_ae (0 : Lp 𝕜 1 unitIntervalMeasure) x,
      Lp.coeFn_zero (Lp 𝕜 1 unitIntervalMeasure) p unitIntervalMeasure] with s ht hz
    rw [ht, smul_zero, hz]
    rfl

end SurveyStatements.P5
