import SurveyStatements.P5MeanZeroCopy
import SurveyStatements.P5Cancellative
import SurveyStatements.P5CompressionComposition

/-! Actual bounded embeddings of the full mixed Bochner space into the
two-kernel cancellative space, obtained by antisymmetrizing both coordinates. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option profiler true
open MeasureTheory Filter
open scoped ENNReal

namespace SurveyStatements.P5

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

def innerCopyInjection : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (meanZeroCopyInjection (𝕜 := 𝕜) (E := 𝕜) (p := 1) (by norm_num)).compLpL
    p unitIntervalMeasure

def innerCopyRetraction : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (meanZeroCopyRetraction (𝕜 := 𝕜) (E := 𝕜) (p := 1) (by norm_num)).compLpL
    p unitIntervalMeasure

theorem innerCopy_retraction :
    (innerCopyRetraction 𝕜 p).comp (innerCopyInjection 𝕜 p) =
      ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p) :=
  lift_retraction _ _ (meanZeroCopy_retraction (by norm_num))

theorem norm_innerCopyInjection_le : ‖innerCopyInjection 𝕜 p‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans (norm_meanZeroCopyInjection_le (by norm_num))

theorem norm_innerCopyRetraction_le : ‖innerCopyRetraction 𝕜 p‖ ≤ 2 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans (norm_meanZeroCopyRetraction_le (by norm_num))

def mixedCopyInjection (hp : p ≠ ∞) : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (innerCopyInjection 𝕜 p).comp
    (meanZeroCopyInjection (𝕜 := 𝕜) (E := Lp 𝕜 1 unitIntervalMeasure) hp)

def mixedCopyRetraction (hp : p ≠ ∞) : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  (meanZeroCopyRetraction (𝕜 := 𝕜) (E := Lp 𝕜 1 unitIntervalMeasure) hp).comp
    (innerCopyRetraction 𝕜 p)

theorem mixedCopy_retraction (hp : p ≠ ∞) :
    (mixedCopyRetraction 𝕜 p hp).comp (mixedCopyInjection 𝕜 p hp) =
      ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p) :=
  compression_composition_retraction (innerCopyRetraction 𝕜 p) (innerCopyInjection 𝕜 p)
    (meanZeroCopyRetraction (𝕜 := 𝕜) (E := Lp 𝕜 1 unitIntervalMeasure) hp)
    (meanZeroCopyInjection (𝕜 := 𝕜) (E := Lp 𝕜 1 unitIntervalMeasure) hp)
    (innerCopy_retraction 𝕜 p) (meanZeroCopy_retraction hp)

theorem norm_mixedCopyInjection_le (hp : p ≠ ∞) : ‖mixedCopyInjection 𝕜 p hp‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (norm_innerCopyInjection_le 𝕜 p) (norm_meanZeroCopyInjection_le hp)
      (norm_nonneg _) zero_le_one).trans (by norm_num))

theorem norm_mixedCopyRetraction_le (hp : p ≠ ∞) : ‖mixedCopyRetraction 𝕜 p hp‖ ≤ 4 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (norm_meanZeroCopyRetraction_le hp) (norm_innerCopyRetraction_le 𝕜 p)
      (norm_nonneg _) (by norm_num)).trans (by norm_num))

end SurveyStatements.P5

