import PEMS.Definitions

noncomputable section
namespace PEMS
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Definition 5.8, pp. 39--40: all four conditions, plus normalization.
The complemented ℓ¹ copy is part of this definition, not an assumed
factorization through the arbitrary operator T being studied. -/
structure NormalizedWeakNoncompactnessMeasure (α : (E →L[𝕜] E) → ℝ) : Prop where
  nonneg : ∀ T, 0 ≤ α T
  add_le : ∀ S T, α (S + T) ≤ α S + α T
  smul_eq : ∀ (a : 𝕜) T, α (a • T) = ‖a‖ * α T
  comp_le_left : ∀ S T : E →L[𝕜] E, α (S.comp T) ≤ ‖S‖ * α T
  comp_le_right : ∀ S T : E →L[𝕜] E, α (S.comp T) ≤ α S * ‖T‖
  zero_iff : ∀ T, α T = 0 ↔ IsWeaklyCompactOperator T
  normalized_copy : ∃ J : EllOne 𝕜 →L[𝕜] E, ∃ P : E →L[𝕜] EllOne 𝕜,
    (∀ x, ‖J x‖ = ‖x‖) ∧ ‖P‖ = 1 ∧
      P.comp J = ContinuousLinearMap.id 𝕜 (EllOne 𝕜) ∧ 1 ≤ α (J.comp P)
  normalized : α (ContinuousLinearMap.id 𝕜 E) = 1

/-- Lemma 5.10 target. The proof applies to any normed space, so the ambient
AL hypothesis used throughout Section 5 is unnecessary for this one lemma. -/
def Lemma_5_10 (α : (E →L[𝕜] E) → ℝ) (T : E →L[𝕜] E) : Prop :=
  NormalizedWeakNoncompactnessMeasure α → α T ≤ weakEssentialNorm T

/-- Proposition 5.11: on an AL-space every normalized measure in Definition 5.8
equals the weak essential norm. The AL and completeness hypotheses are retained;
the separate conditional assembly lemma does not prove this target. -/
def Proposition_5_11 [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
    (α : (E →L[𝕜] E) → ℝ) (T : E →L[𝕜] E) : Prop :=
  IsALSpace 𝕜 E → NormalizedWeakNoncompactnessMeasure α → α T = weakEssentialNorm T

end PEMS
