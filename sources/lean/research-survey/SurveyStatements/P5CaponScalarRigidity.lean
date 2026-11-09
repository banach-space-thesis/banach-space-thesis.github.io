import SurveyStatements.P5CaponUnboundedReal
import SurveyStatements.P5HaarMultipliers

/-! A bounded operator with two constant triangular Haar symbols must have
equal symbols. Otherwise their difference constructs a bounded Capon operator. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal

namespace SurveyStatements.P5
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation

theorem real_triangular_symbols_eq (hp_finite : p ≠ ∞)
    (T : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p) (a b : ℝ)
    (hT : ∀ I J, T (productHaar ℝ p I J) =
      if J.1 ≤ I.1 then a • productHaar ℝ p I J else b • productHaar ℝ p I J) :
    a = b := by
  by_contra hne
  have hab : a - b ≠ 0 := sub_ne_zero.mpr hne
  let C : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p :=
    (a - b)⁻¹ • (T - b • ContinuousLinearMap.id ℝ (MixedNorm ℝ p))
  apply no_real_capon_operator hp_finite C
  intro I J
  change (a - b)⁻¹ • (T (productHaar ℝ p I J) - b • productHaar ℝ p I J) = _
  rw [hT]
  by_cases h : J.1 ≤ I.1
  · rw [if_pos h, if_pos h, ← sub_smul, smul_smul, inv_mul_cancel₀ hab, one_smul]
  · rw [if_neg h, if_neg h, sub_self, smul_zero]

theorem real_cancellative_triangular_symbols_eq (hp_finite : p ≠ ∞)
    (T : DoublyZeroMean ℝ p →L[ℝ] DoublyZeroMean ℝ p) (a b : ℝ)
    (hT : ∀ I J, T (cancellativeHaar ℝ p I J) =
      if J.1 ≤ I.1 then a • cancellativeHaar ℝ p I J
        else b • cancellativeHaar ℝ p I J) : a = b := by
  let S : MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p :=
    (DoublyZeroMean ℝ p).subtypeL.comp (T.comp (cancellativeProjection ℝ p))
  apply real_triangular_symbols_eq hp_finite S a b
  intro I J
  have hfix : cancellativeProjection ℝ p (productHaar ℝ p I J) =
      cancellativeHaar ℝ p I J :=
    congrArg (fun L : DoublyZeroMean ℝ p →L[ℝ] DoublyZeroMean ℝ p =>
      L (cancellativeHaar ℝ p I J)) (cancellativeProjection_retraction ℝ p)
  change (T (cancellativeProjection ℝ p (productHaar ℝ p I J))).val = _
  rw [hfix, hT]
  split <;> rfl

theorem real_cancellative_triangular_operator_eq_scalar (hp_finite : p ≠ ∞)
    (T : DoublyZeroMean ℝ p →L[ℝ] DoublyZeroMean ℝ p) (a b : ℝ)
    (hT : ∀ I J, T (cancellativeHaar ℝ p I J) =
      if J.1 ≤ I.1 then a • cancellativeHaar ℝ p I J
        else b • cancellativeHaar ℝ p I J) :
    T = a • ContinuousLinearMap.id ℝ (DoublyZeroMean ℝ p) := by
  have hab := real_cancellative_triangular_symbols_eq hp_finite T a b hT
  apply cancellativeOperators_eq_of_haar hp_finite
  intro I J
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hT, hab,
    ite_self]

end SurveyStatements.P5
