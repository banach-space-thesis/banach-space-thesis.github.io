import SurveyStatements.P5OperatorReductionPacketShadowBounds
import SurveyStatements.P5OperatorReductionRawShadows
import SurveyStatements.P5TensorBilinearity

/-! The packet shadows are actual bounded L1 operators, uniformly bounded
by the original mixed operator. This supplies the primal-side functional
families in the opposite-coordinate finite selection step. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 ι : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def packetShadowOperator (k : ι → ℕ)
    (f : ∀ i, (Fin (k i) → Bool) → Lp 𝕜 p unitIntervalMeasure)
    (η : ∀ i, (Fin (k i) → Bool) → ℝ → 𝕜)
    (hη : ∀ i θ, StronglyMeasurable (η i θ))
    (hb : ∀ i θ x, ‖η i θ x‖ ≤ 1)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) (i : ι) :
    Lp 𝕜 1 unitIntervalMeasure →L[𝕜] Lp 𝕜 1 unitIntervalMeasure :=
  (((Fintype.card (Fin (k i) → Bool) : ℝ)⁻¹ : ℝ) : 𝕜) •
    ∑ θ : Fin (k i) → Bool,
      (weightedOuterReader (𝕜 := 𝕜) (p := p) (E := Lp 𝕜 1 unitIntervalMeasure)
        (η i θ) (hη i θ) (hb i θ)).comp (T.comp (tensorInnerMap (f i θ)))

theorem packetShadowOperator_apply (k : ι → ℕ)
    (f : ∀ i, (Fin (k i) → Bool) → Lp 𝕜 p unitIntervalMeasure)
    (η : ∀ i, (Fin (k i) → Bool) → ℝ → 𝕜)
    (hη : ∀ i θ, StronglyMeasurable (η i θ))
    (hb : ∀ i θ x, ‖η i θ x‖ ≤ 1)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) (i : ι)
    (g : Lp 𝕜 1 unitIntervalMeasure) :
    packetShadowOperator k f η hη hb T i g = packetShadow k f η hη hb T g i := by
  simp only [packetShadowOperator, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, packetShadow,
    vectorMean] <;> rfl

theorem norm_packetShadowOperator_le (k : ι → ℕ)
    (f : ∀ i, (Fin (k i) → Bool) → Lp 𝕜 p unitIntervalMeasure)
    (hf : ∀ i θ, ∀ᵐ x ∂unitIntervalMeasure, ‖f i θ x‖ ≤ 1)
    (η : ∀ i, (Fin (k i) → Bool) → ℝ → 𝕜)
    (hη : ∀ i θ, StronglyMeasurable (η i θ))
    (hb : ∀ i θ x, ‖η i θ x‖ ≤ 1)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) (i : ι) :
    ‖packetShadowOperator k f η hη hb T i‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro g
  rw [packetShadowOperator_apply]
  exact norm_packetShadow_le k f hf η hη hb T g i

end SurveyStatements.P5OperatorReduction
