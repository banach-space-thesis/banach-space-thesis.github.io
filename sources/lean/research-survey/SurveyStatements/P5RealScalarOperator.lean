import SurveyStatements.P5RealScalarHaar

/-! Restrict an arbitrary complex operator to the real copy and read its
real part. Real product-Haar eigenvalues are preserved by this operation. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5.RealScalar

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

def operator (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) :
    MixedNorm ℝ p →L[ℝ] MixedNorm ℝ p :=
  (retraction 𝕜 p).comp ((T.restrictScalars ℝ).comp (embedding 𝕜 p))

theorem norm_operator_le (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) :
    ‖operator 𝕜 p T‖ ≤ ‖T‖ := by
  have hTE : ‖(T.restrictScalars ℝ).comp (embedding 𝕜 p)‖ ≤ ‖T‖ := by
    calc
      _ ≤ ‖T.restrictScalars ℝ‖ * ‖embedding 𝕜 p‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T.restrictScalars ℝ‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_embedding_le 𝕜 p)
          (ContinuousLinearMap.opNorm_nonneg (T.restrictScalars ℝ))
      _ = ‖T‖ := by rw [mul_one, ContinuousLinearMap.norm_restrictScalars]
  calc
    ‖operator 𝕜 p T‖ ≤ ‖retraction 𝕜 p‖ *
        ‖(T.restrictScalars ℝ).comp (embedding 𝕜 p)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T‖ := mul_le_mul (norm_retraction_le 𝕜 p) hTE
      (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
    _ = ‖T‖ := one_mul _

theorem operator_productHaar
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) (d : DyadicIndex → DyadicIndex → ℝ)
    (hT : ∀ I J, T (productHaar 𝕜 p I J) = (d I J : 𝕜) • productHaar 𝕜 p I J)
    (I J : DyadicIndex) :
    operator 𝕜 p T (productHaar ℝ p I J) = d I J • productHaar ℝ p I J := by
  change retraction 𝕜 p (T (embedding 𝕜 p (productHaar ℝ p I J))) = _
  rw [embedding_productHaar, hT]
  rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜), map_smul, retraction_productHaar]

theorem operator_productHaar_cut
    (T : MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p)
    (hT : ∀ I J, T (productHaar 𝕜 p I J) =
      if J.1 ≤ I.1 then productHaar 𝕜 p I J else 0) (I J : DyadicIndex) :
    operator 𝕜 p T (productHaar ℝ p I J) =
      if J.1 ≤ I.1 then productHaar ℝ p I J else 0 := by
  change retraction 𝕜 p (T (embedding 𝕜 p (productHaar ℝ p I J))) = _
  rw [embedding_productHaar, hT]
  by_cases h : J.1 ≤ I.1
  · rw [if_pos h, if_pos h, retraction_productHaar]
  · rw [if_neg h, if_neg h, map_zero]

end SurveyStatements.P5.RealScalar
