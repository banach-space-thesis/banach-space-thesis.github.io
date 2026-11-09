import SurveyStatements.P5Averages
import Mathlib.Analysis.RCLike.Lemmas

/-! The real embedding and real-part retraction on the actual nested
Bochner space. These are real-linear maps; they do not assert a complex-linear
compression of an arbitrary operator. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5.RealScalar

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem lifted_retraction (A : E →L[ℝ] F) (B : F →L[ℝ] E)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ E) :
    (B.compLpL q unitIntervalMeasure).comp (A.compLpL q unitIntervalMeasure) =
      ContinuousLinearMap.id ℝ (Lp E q unitIntervalMeasure) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [B.coeFn_compLpL (A.compLpL q unitIntervalMeasure f),
    A.coeFn_compLpL f] with x hB hA
  change (B.compLpL q unitIntervalMeasure (A.compLpL q unitIntervalMeasure f)) x = f x
  rw [hB, hA]
  exact congrArg (fun L : E →L[ℝ] E => L (f x)) hBA

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

def scalarEmbedding : Lp ℝ p unitIntervalMeasure →L[ℝ] Lp 𝕜 p unitIntervalMeasure :=
  (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLpL p unitIntervalMeasure

def scalarRetraction : Lp 𝕜 p unitIntervalMeasure →L[ℝ] Lp ℝ p unitIntervalMeasure :=
  (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).compLpL p unitIntervalMeasure

theorem norm_scalarEmbedding_le : ‖scalarEmbedding 𝕜 p‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans_eq (RCLike.ofRealCLM_norm (K := 𝕜))

theorem norm_scalarRetraction_le : ‖scalarRetraction 𝕜 p‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans_eq (RCLike.reCLM_norm (K := 𝕜))

theorem scalar_retraction :
    (scalarRetraction 𝕜 p).comp (scalarEmbedding 𝕜 p) =
      ContinuousLinearMap.id ℝ (Lp ℝ p unitIntervalMeasure) := by
  apply lifted_retraction
  apply ContinuousLinearMap.ext
  intro x
  exact RCLike.ofReal_re x

def embedding : MixedNorm ℝ p →L[ℝ] MixedNorm 𝕜 p :=
  (scalarEmbedding 𝕜 1).compLpL p unitIntervalMeasure

def retraction : MixedNorm 𝕜 p →L[ℝ] MixedNorm ℝ p :=
  (scalarRetraction 𝕜 1).compLpL p unitIntervalMeasure

theorem norm_embedding_le : ‖embedding 𝕜 p‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans (norm_scalarEmbedding_le 𝕜 1)

theorem norm_retraction_le : ‖retraction 𝕜 p‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans (norm_scalarRetraction_le 𝕜 1)

theorem retraction_embedding :
    (retraction 𝕜 p).comp (embedding 𝕜 p) = ContinuousLinearMap.id ℝ (MixedNorm ℝ p) :=
  lifted_retraction _ _ (scalar_retraction 𝕜 1)

theorem retraction_embedding_apply (f : MixedNorm ℝ p) :
    retraction 𝕜 p (embedding 𝕜 p f) = f :=
  congrArg (fun L : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p => L f)
    (retraction_embedding 𝕜 p)

theorem norm_embedding_apply (f : MixedNorm ℝ p) : ‖embedding 𝕜 p f‖ = ‖f‖ := by
  apply le_antisymm
  · exact ((embedding 𝕜 p).le_opNorm f).trans
      ((mul_le_mul_of_nonneg_right (norm_embedding_le 𝕜 p) (norm_nonneg f)).trans_eq
        (one_mul _))
  · calc
      ‖f‖ = ‖retraction 𝕜 p (embedding 𝕜 p f)‖ := by rw [retraction_embedding_apply]
      _ ≤ ‖retraction 𝕜 p‖ * ‖embedding 𝕜 p f‖ := (retraction 𝕜 p).le_opNorm _
      _ ≤ 1 * ‖embedding 𝕜 p f‖ :=
        mul_le_mul_of_nonneg_right (norm_retraction_le 𝕜 p) (norm_nonneg _)
      _ = ‖embedding 𝕜 p f‖ := one_mul _

end SurveyStatements.P5.RealScalar
