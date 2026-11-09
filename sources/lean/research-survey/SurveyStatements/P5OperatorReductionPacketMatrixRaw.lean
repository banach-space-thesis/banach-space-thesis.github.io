import SurveyStatements.P5OperatorReductionPacketMatrixDecay

/-! The normalized same-level matrix is exactly the raw Haar coefficient
matrix: the common level normalization cancels for every pair of indices. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical ENNReal

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem packetMatrix_normalizedEntry_eq_raw_sameLevel
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (i j : Fin (2 ^ n)) :
    lpHaarNormalizedCoordinate 𝕜 p (some ⟨n, i⟩)
      (Q (lpHaarNormalizedVector 𝕜 p (some ⟨n, j⟩))) =
        lpHaarDyadicCoefficient 𝕜 p n i (Q (lpHaarDyadic 𝕜 p n j)) := by
  have hc : ((intervalLpDyadicRadius n ^ (1 / p.val.toReal) : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (intervalLpDyadicRadius_pos n) (1 / p.val.toReal)).ne'
  simp only [lpHaarNormalizedCoordinate, lpHaarNormalizedVector,
    ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul,
    lpHaarRawVector, lpHaarRawCoordinate,
    lpHaarDyadic_norm 𝕜 p hp n i i.isLt, lpHaarDyadic_norm 𝕜 p hp n j j.isLt]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

def operatorReductionRawPacketMatrix (p : BanachExponent)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (i j : Fin S.card) : 𝕜 :=
  lpHaarDyadicCoefficient 𝕜 p n (S.orderEmbOfFin rfl i)
    (Q (lpHaarDyadic 𝕜 p n (S.orderEmbOfFin rfl j)))

theorem operatorReductionPacketMatrix_eq_raw
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    operatorReductionPacketMatrix p Q n S = operatorReductionRawPacketMatrix p Q n S := by
  funext i j
  exact packetMatrix_normalizedEntry_eq_raw_sameLevel p hp Q n _ _

theorem operatorReductionPacketMatrixVariance_eq_raw
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    operatorReductionPacketMatrixVariance p Q n S =
      mean (fun θ : Fin S.card → Bool =>
        ‖(S.card : 𝕜)⁻¹ * centeredQuadraticForm
          (operatorReductionRawPacketMatrix p Q n S) θ‖ ^ 2) := by
  unfold operatorReductionPacketMatrixVariance
  rw [operatorReductionPacketMatrix_eq_raw p hp]

end SurveyStatements.P5OperatorReduction
