import SurveyStatements.P5RealScalarOperator
import SurveyStatements.P5RealScalarRestricted
import SurveyStatements.P5CaponUnboundedReal

/-! Capon's product-Haar cut cannot extend to a bounded operator over any
RCLike field, on the mixed space or its doubly cancellative subspace. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5

variable (𝕜 : Type*) [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem no_capon_operator (hp_finite : p ≠ ∞)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) :
    ¬ (∀ I J, T (productHaar 𝕜 p I J) =
      if J.1 ≤ I.1 then productHaar 𝕜 p I J else 0) := by
  intro hT
  apply no_real_capon_operator hp_finite (RealScalar.operator 𝕜 p T)
  intro I J
  exact RealScalar.operator_productHaar_cut 𝕜 p T hT I J

theorem no_cancellative_capon_operator (hp_finite : p ≠ ∞)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p) :
    ¬ (∀ I J, T (cancellativeHaar 𝕜 p I J) =
      if J.1 ≤ I.1 then cancellativeHaar 𝕜 p I J else 0) := by
  intro hT
  let S : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
    (DoublyZeroMean 𝕜 p).subtypeL.comp (T.comp (cancellativeProjection 𝕜 p))
  apply no_capon_operator 𝕜 hp_finite S
  intro I J
  have hfix : cancellativeProjection 𝕜 p (productHaar 𝕜 p I J) =
      cancellativeHaar 𝕜 p I J := by
    exact congrArg (fun L : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p =>
      L (cancellativeHaar 𝕜 p I J)) (cancellativeProjection_retraction 𝕜 p)
  change (T (cancellativeProjection 𝕜 p (productHaar 𝕜 p I J))).val = _
  rw [hfix, hT]
  split <;> rfl

end SurveyStatements.P5
