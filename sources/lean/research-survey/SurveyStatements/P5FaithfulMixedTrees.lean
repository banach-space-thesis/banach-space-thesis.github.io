import SurveyStatements.P5VectorTreeKernels
import SurveyStatements.P5RestrictedRetractions
import SurveyStatements.P5HalfCopy
import SurveyStatements.P5CompressionComposition

/-! Faithful trees in the two coordinates yield actual contractive
retractions of the doubly cancellative Bochner Lp(L1) space. The maps are
constructed from the checked strong limits, not postulated. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace SurveyStatements.P5

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_faithful_mixed_retraction (hp : p ≠ ∞)
    (Ho Hi : P5Support.LpHaarPartitionTree)
    (hHo : Ho.FaithfulSplits) (hHi : Hi.FaithfulSplits) :
    ∃ A B : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p,
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      A.comp B = ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p) ∧
      ∀ f, ‖B f‖ = ‖f‖ := by
  obtain ⟨Ao, Bo, hAo, hBo, hAoBo, _, hAolim, hBolim⟩ :=
    VectorPartitionTree.exists_faithful_retraction
      (𝕜 := 𝕜) (E := Lp 𝕜 1 unitIntervalMeasure) Ho hp hHo
  obtain ⟨Ai, Bi, hAi, hBi, hAiBi, _, hAilim, hBilim⟩ :=
    VectorPartitionTree.exists_faithful_retraction
      (𝕜 := 𝕜) (E := 𝕜) (p := 1) Hi (by simp) hHi
  have hAintegral (f : Lp 𝕜 1 unitIntervalMeasure) :
      probabilityLpIntegral (𝕜 := 𝕜) (Ai f) = probabilityLpIntegral (𝕜 := 𝕜) f :=
    VectorPartitionTree.backward_limit_integral Hi (by simp) hHi Ai hAilim f
  have hBintegral (f : Lp 𝕜 1 unitIntervalMeasure) :
      probabilityLpIntegral (𝕜 := 𝕜) (Bi f) = probabilityLpIntegral (𝕜 := 𝕜) f :=
    VectorPartitionTree.forward_limit_integral Hi (by simp) Bi hBilim f
  let A := (Ai.compLpL p unitIntervalMeasure).comp Ao
  let B := Bo.comp (Bi.compLpL p unitIntervalMeasure)
  have hAlift : ‖Ai.compLpL p unitIntervalMeasure‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans hAi
  have hBlift : ‖Bi.compLpL p unitIntervalMeasure‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans hBi
  have hA : ‖A‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hAlift hAo (norm_nonneg _) zero_le_one).trans (by simp))
  have hB : ‖B‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hBo hBlift (norm_nonneg _) zero_le_one).trans (by simp))
  have hAB : A.comp B = ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p) :=
    compression_composition_retraction Ao Bo _ _ hAoBo (lift_retraction Ai Bi hAiBi)
  have hAS (f : MixedNorm 𝕜 p) (hf : f ∈ DoublyZeroMean 𝕜 p) :
      A f ∈ DoublyZeroMean 𝕜 p :=
    innerLift_mem_doublyZeroMean Ai hAintegral (Ao f)
      (VectorPartitionTree.backward_limit_mem_doublyZeroMean Ho hp hHo Ao hAolim f hf)
  have hBS (f : MixedNorm 𝕜 p) (hf : f ∈ DoublyZeroMean 𝕜 p) :
      B f ∈ DoublyZeroMean 𝕜 p :=
    VectorPartitionTree.forward_limit_mem_doublyZeroMean Ho hp Bo hBolim _
      (innerLift_mem_doublyZeroMean Bi hBintegral f hf)
  exact exists_restricted_contractive_retraction (DoublyZeroMean 𝕜 p)
    A B hA hB hAB hAS hBS

end SurveyStatements.P5
