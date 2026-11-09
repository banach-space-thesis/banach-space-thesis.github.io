import SurveyStatements.P5RealScalarMeans
import SurveyStatements.P5RealScalarHaar
import SurveyStatements.P5HaarDiagonalBounds

/-! The actual real embedding/retraction pair on the intersection of the
two expectation kernels. The target is the same complex cancellative carrier
equipped with its inherited real scalar action. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5.RealScalar

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

abbrev RealCancellative := (DoublyZeroMean 𝕜 p).restrictScalars ℝ

def cancellativeEmbedding : DoublyZeroMean ℝ p →L[ℝ] RealCancellative 𝕜 p :=
  ((embedding 𝕜 p).comp (DoublyZeroMean ℝ p).subtypeL).codRestrict
    (RealCancellative 𝕜 p) (fun f => embedding_mem_doublyZeroMean 𝕜 p f.val f.property)

def cancellativeRetraction : RealCancellative 𝕜 p →L[ℝ] DoublyZeroMean ℝ p :=
  ((retraction 𝕜 p).comp (RealCancellative 𝕜 p).subtypeL).codRestrict
    (DoublyZeroMean ℝ p) (fun f => retraction_mem_doublyZeroMean 𝕜 p f.val f.property)

@[simp] theorem cancellativeEmbedding_val (f : DoublyZeroMean ℝ p) :
    (cancellativeEmbedding 𝕜 p f).val = embedding 𝕜 p f.val := rfl

@[simp] theorem cancellativeRetraction_val (f : RealCancellative 𝕜 p) :
    (cancellativeRetraction 𝕜 p f).val = retraction 𝕜 p f.val := rfl

theorem norm_cancellativeEmbedding_le : ‖cancellativeEmbedding 𝕜 p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖embedding 𝕜 p f.val‖ ≤ 1 * ‖f.val‖
  exact ((embedding 𝕜 p).le_opNorm f.val).trans
    (mul_le_mul_of_nonneg_right (norm_embedding_le 𝕜 p) (norm_nonneg _))

theorem norm_cancellativeRetraction_le : ‖cancellativeRetraction 𝕜 p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖retraction 𝕜 p f.val‖ ≤ 1 * ‖f.val‖
  exact ((retraction 𝕜 p).le_opNorm f.val).trans
    (mul_le_mul_of_nonneg_right (norm_retraction_le 𝕜 p) (norm_nonneg _))

theorem cancellative_retraction :
    (cancellativeRetraction 𝕜 p).comp (cancellativeEmbedding 𝕜 p) =
      ContinuousLinearMap.id ℝ (DoublyZeroMean ℝ p) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact retraction_embedding_apply 𝕜 p f.val

theorem norm_cancellativeEmbedding_apply (f : DoublyZeroMean ℝ p) :
    ‖cancellativeEmbedding 𝕜 p f‖ = ‖f‖ := norm_embedding_apply 𝕜 p f.val

theorem cancellativeEmbedding_haar (I J : DyadicIndex) :
    cancellativeEmbedding 𝕜 p (cancellativeHaar ℝ p I J) = cancellativeHaar 𝕜 p I J := by
  apply Subtype.ext
  exact embedding_productHaar 𝕜 p I J

theorem cancellativeRetraction_haar (I J : DyadicIndex) :
    cancellativeRetraction 𝕜 p (cancellativeHaar 𝕜 p I J) = cancellativeHaar ℝ p I J := by
  apply Subtype.ext
  exact retraction_productHaar 𝕜 p I J

end SurveyStatements.P5.RealScalar
