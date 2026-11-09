import SurveyStatements.P5RealScalarCapon
import SurveyStatements.P5HaarMultipliers

/-! Two constant triangular symbols of a bounded cancellative Haar operator
are equal over the original scalar field. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ENNReal

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation

theorem triangular_symbols_eq (hp_finite : p ≠ ∞)
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) (a b : 𝕜)
    (hT : ∀ I J, T (productHaar 𝕜 p I J) =
      if J.1 ≤ I.1 then a • productHaar 𝕜 p I J else b • productHaar 𝕜 p I J) :
    a = b := by
  by_contra hne
  have hab : a - b ≠ 0 := sub_ne_zero.mpr hne
  let C : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
    (a - b)⁻¹ • (T - b • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p))
  apply no_capon_operator 𝕜 hp_finite C
  intro I J
  change (a - b)⁻¹ • (T (productHaar 𝕜 p I J) - b • productHaar 𝕜 p I J) = _
  rw [hT]
  by_cases h : J.1 ≤ I.1
  · rw [if_pos h, if_pos h, ← sub_smul, smul_smul, inv_mul_cancel₀ hab, one_smul]
  · rw [if_neg h, if_neg h, sub_self, smul_zero]

theorem cancellative_triangular_symbols_eq (hp_finite : p ≠ ∞)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p) (a b : 𝕜)
    (hT : ∀ I J, T (cancellativeHaar 𝕜 p I J) =
      if J.1 ≤ I.1 then a • cancellativeHaar 𝕜 p I J
        else b • cancellativeHaar 𝕜 p I J) : a = b := by
  let S : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
    (DoublyZeroMean 𝕜 p).subtypeL.comp (T.comp (cancellativeProjection 𝕜 p))
  apply triangular_symbols_eq hp_finite S a b
  intro I J
  have hfix : cancellativeProjection 𝕜 p (productHaar 𝕜 p I J) =
      cancellativeHaar 𝕜 p I J :=
    congrArg (fun L : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p =>
      L (cancellativeHaar 𝕜 p I J)) (cancellativeProjection_retraction 𝕜 p)
  change (T (cancellativeProjection 𝕜 p (productHaar 𝕜 p I J))).val = _
  rw [hfix, hT]
  split <;> rfl

theorem cancellative_triangular_operator_eq_scalar (hp_finite : p ≠ ∞)
    (T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p) (a b : 𝕜)
    (hT : ∀ I J, T (cancellativeHaar 𝕜 p I J) =
      if J.1 ≤ I.1 then a • cancellativeHaar 𝕜 p I J
        else b • cancellativeHaar 𝕜 p I J) :
    T = a • ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p) := by
  have hab := cancellative_triangular_symbols_eq hp_finite T a b hT
  apply cancellativeOperators_eq_of_haar hp_finite
  intro I J
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hT, hab,
    ite_self]

end SurveyStatements.P5
