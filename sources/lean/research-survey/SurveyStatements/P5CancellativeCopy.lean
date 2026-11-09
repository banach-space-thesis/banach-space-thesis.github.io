import SurveyStatements.P5MixedCopy
import SurveyStatements.P5SubmoduleCopies

/-! Actual bounded embeddings of the full mixed Bochner space into the
two-kernel cancellative space, obtained by antisymmetrizing both coordinates. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option profiler true
open MeasureTheory Filter
open scoped ENNReal

namespace SurveyStatements.P5
attribute [local irreducible] vectorLpBlockEquiv
  vectorLpAffine

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem mixedCopyInjection_mem (hp : p ≠ ∞) (f : MixedNorm 𝕜 p) :
    mixedCopyInjection 𝕜 p hp f ∈ DoublyZeroMean 𝕜 p := by
  constructor
  · exact lifted_map_preserves_zero_mean
      (meanZeroCopyInjection (𝕜 := 𝕜) (E := 𝕜) (p := 1) (by norm_num))
      (meanZeroCopyInjection (𝕜 := 𝕜) hp f) (meanZeroCopyInjection_mean_zero hp f)
  · exact lift_maps_into_kernel probabilityLpMean
      (meanZeroCopyInjection (𝕜 := 𝕜) (E := 𝕜) (p := 1) (by norm_num))
      (meanZeroCopyInjection_mean_zero (by norm_num))
      (meanZeroCopyInjection (𝕜 := 𝕜) hp f)

def cancellativeCopyInjection (hp : p ≠ ∞) : MixedNorm 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
  (mixedCopyInjection 𝕜 p hp).codRestrict (DoublyZeroMean 𝕜 p) (mixedCopyInjection_mem 𝕜 p hp)

def cancellativeCopyRetraction (hp : p ≠ ∞) : DoublyZeroMean 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (mixedCopyRetraction 𝕜 p hp).comp (DoublyZeroMean 𝕜 p).subtypeL

theorem cancellativeCopy_retraction (hp : p ≠ ∞) :
    (cancellativeCopyRetraction 𝕜 p hp).comp (cancellativeCopyInjection 𝕜 p hp) =
      ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p) :=
  codRestrict_retraction (DoublyZeroMean 𝕜 p) (mixedCopyInjection 𝕜 p hp)
    (mixedCopyRetraction 𝕜 p hp) (mixedCopyInjection_mem 𝕜 p hp)
    (mixedCopy_retraction 𝕜 p hp)

theorem norm_cancellativeCopyInjection_le (hp : p ≠ ∞) :
    ‖cancellativeCopyInjection 𝕜 p hp‖ ≤ 1 :=
  (norm_codRestrict_le (DoublyZeroMean 𝕜 p) (mixedCopyInjection 𝕜 p hp)
    (mixedCopyInjection_mem 𝕜 p hp)).trans (norm_mixedCopyInjection_le 𝕜 p hp)

theorem norm_cancellativeCopyRetraction_le (hp : p ≠ ∞) :
    ‖cancellativeCopyRetraction 𝕜 p hp‖ ≤ 4 :=
  (norm_comp_subtype_le (DoublyZeroMean 𝕜 p) (mixedCopyRetraction 𝕜 p hp)).trans
    (norm_mixedCopyRetraction_le 𝕜 p hp)

end SurveyStatements.P5

