import SurveyStatements.P5OperatorReductionPacketMatrixRows
import SurveyStatements.P5OperatorReductionMoments

/-! Coarse square-sum and centered quadratic variance estimates for the
actual normalized Haar matrix of an arbitrary bounded scalar Lp operator. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical ENNReal

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem operatorReductionPacketMatrix_row_square_sum_le
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (i : Fin S.card) :
    (∑ j : Fin S.card, ‖operatorReductionPacketMatrix p Q n S i j‖ ^ 2) ≤
      36 * ‖Q‖ ^ 2 * (S.card : ℝ) ^ (1 / p.val.toReal) := by
  calc
    _ ≤ ∑ j : Fin S.card, (6 * ‖Q‖) * ‖operatorReductionPacketMatrix p Q n S i j‖ := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [pow_two] using mul_le_mul_of_nonneg_right
        (operatorReductionPacketMatrix_entry_norm_le p hp Q n S i j) (norm_nonneg _)
    _ = (6 * ‖Q‖) * ∑ j : Fin S.card, ‖operatorReductionPacketMatrix p Q n S i j‖ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (6 * ‖Q‖) * (6 * ‖Q‖ * (S.card : ℝ) ^ (1 / p.val.toReal)) :=
      mul_le_mul_of_nonneg_left (operatorReductionPacketMatrix_row_sum_le p hp Q n S i)
        (by positivity)
    _ = _ := by ring

theorem operatorReductionPacketMatrix_square_sum_le
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    (∑ i : Fin S.card, ∑ j : Fin S.card,
      ‖operatorReductionPacketMatrix p Q n S i j‖ ^ 2) ≤
        36 * ‖Q‖ ^ 2 * (S.card : ℝ) * (S.card : ℝ) ^ (1 / p.val.toReal) := by
  calc
    _ ≤ ∑ _i : Fin S.card, 36 * ‖Q‖ ^ 2 * (S.card : ℝ) ^ (1 / p.val.toReal) :=
      Finset.sum_le_sum (fun i _ => operatorReductionPacketMatrix_row_square_sum_le p hp Q n S i)
    _ = (S.card : ℝ) * (36 * ‖Q‖ ^ 2 * (S.card : ℝ) ^ (1 / p.val.toReal)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := by ring

theorem operatorReductionPacketMatrix_offDiagonalSquareSum_le
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    offDiagonalSquareSum (operatorReductionPacketMatrix p Q n S) ≤
      36 * ‖Q‖ ^ 2 * (S.card : ℝ) * (S.card : ℝ) ^ (1 / p.val.toReal) := by
  apply le_trans _ (operatorReductionPacketMatrix_square_sum_le p hp Q n S)
  unfold offDiagonalSquareSum
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

def operatorReductionPacketMatrixVariance (p : BanachExponent)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) : ℝ :=
  mean (fun θ : Fin S.card → Bool =>
    ‖(S.card : 𝕜)⁻¹ * centeredQuadraticForm (operatorReductionPacketMatrix p Q n S) θ‖ ^ 2)

theorem operatorReductionPacketMatrixVariance_nonneg
    (p : BanachExponent) (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) : 0 ≤ operatorReductionPacketMatrixVariance p Q n S :=
  mean_nonneg (fun _ => sq_nonneg _)

theorem operatorReductionPacketMatrix_variance_le_inverse_card
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    operatorReductionPacketMatrixVariance p Q n S ≤
      72 * ‖Q‖ ^ 2 * ((S.card : ℝ)⁻¹) ^ 2 *
        (S.card : ℝ) * (S.card : ℝ) ^ (1 / p.val.toReal) := by
  calc
    _ ≤ 2 * ((S.card : ℝ)⁻¹) ^ 2 *
        offDiagonalSquareSum (operatorReductionPacketMatrix p Q n S) :=
      normalized_centeredQuadraticForm_variance_le _
    _ ≤ 2 * ((S.card : ℝ)⁻¹) ^ 2 *
        (36 * ‖Q‖ ^ 2 * (S.card : ℝ) * (S.card : ℝ) ^ (1 / p.val.toReal)) :=
      mul_le_mul_of_nonneg_left
        (operatorReductionPacketMatrix_offDiagonalSquareSum_le p hp Q n S) (by positivity)
    _ = _ := by ring

theorem operatorReductionPacketMatrix_variance_le_power
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (hS : S.Nonempty) :
    operatorReductionPacketMatrixVariance p Q n S ≤
      72 * ‖Q‖ ^ 2 * (S.card : ℝ) ^ (1 / p.val.toReal - 1) := by
  have hN : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hS).ne'
  have hfactor : ((S.card : ℝ)⁻¹) ^ 2 * (S.card : ℝ) *
      (S.card : ℝ) ^ (1 / p.val.toReal) = (S.card : ℝ) ^ (1 / p.val.toReal - 1) := by
    rw [Real.rpow_sub_one hN]
    field_simp <;> ring
  calc
    _ ≤ 72 * ‖Q‖ ^ 2 * ((S.card : ℝ)⁻¹) ^ 2 *
        (S.card : ℝ) * (S.card : ℝ) ^ (1 / p.val.toReal) :=
      operatorReductionPacketMatrix_variance_le_inverse_card p hp Q n S
    _ = (72 * ‖Q‖ ^ 2) *
        (((S.card : ℝ)⁻¹) ^ 2 * (S.card : ℝ) * (S.card : ℝ) ^ (1 / p.val.toReal)) := by ring
    _ = _ := by rw [hfactor]

end SurveyStatements.P5OperatorReduction
