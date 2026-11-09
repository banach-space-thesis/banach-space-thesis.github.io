import SurveyStatements.P5VectorTreeIntegral
import SurveyStatements.P5MeanPreservingLifts

/-! Actual exterior Haar-tree limits preserve the intersection of the two
expectation kernels defining the paper's cancellative mixed space. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace SurveyStatements.P5.VectorPartitionTree

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (H : P5Support.LpHaarPartitionTree)

theorem backward_limit_mem_doublyZeroMean (hp : p ≠ ∞) (hH : H.FaithfulSplits)
    (A : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hA : ∀ f, Tendsto (fun n => backward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (A f)))
    (f : MixedNorm 𝕜 p) (hf : f ∈ DoublyZeroMean 𝕜 p) :
    A f ∈ DoublyZeroMean 𝕜 p := by
  constructor
  · change probabilityLpMean (𝕜 := 𝕜) (A f) = 0
    rw [probabilityLpMean_apply, backward_limit_integral H hp hH A hA,
      ← probabilityLpMean_apply]
    exact hf.1
  · change innerExpectation 𝕜 p (A f) = 0
    have hn := backward_limit_natural H hp A A hA hA
      (probabilityLpMean (𝕜 := 𝕜) (E := 𝕜) (p := 1)
        (μ := unitIntervalMeasure)) f
    change A (innerExpectation 𝕜 p f) = innerExpectation 𝕜 p (A f) at hn
    rw [← hn, hf.2, map_zero]

theorem forward_limit_mem_doublyZeroMean (hp : p ≠ ∞)
    (B : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hB : ∀ f, Tendsto (fun n => forward (𝕜 := 𝕜) H hp n f) atTop (𝓝 (B f)))
    (f : MixedNorm 𝕜 p) (hf : f ∈ DoublyZeroMean 𝕜 p) :
    B f ∈ DoublyZeroMean 𝕜 p := by
  constructor
  · change probabilityLpMean (𝕜 := 𝕜) (B f) = 0
    rw [probabilityLpMean_apply, forward_limit_integral H hp B hB,
      ← probabilityLpMean_apply]
    exact hf.1
  · change innerExpectation 𝕜 p (B f) = 0
    have hn := forward_limit_natural H hp B B hB hB
      (probabilityLpMean (𝕜 := 𝕜) (E := 𝕜) (p := 1)
        (μ := unitIntervalMeasure)) f
    change B (innerExpectation 𝕜 p f) = innerExpectation 𝕜 p (B f) at hn
    rw [← hn, hf.2, map_zero]

end SurveyStatements.P5.VectorPartitionTree
