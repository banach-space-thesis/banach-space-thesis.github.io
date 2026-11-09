import SurveyStatements.P5OperatorReductionInnerMatrixRestrictions
import SurveyStatements.P5OperatorReductionPacketMatrixPhases

/-! Actual normalized same-level L1 operator matrices have columns of
absolute sum at most the operator norm, without any structural hypothesis. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem operatorReductionInnerMatrix_column_sum_le
    (Q : IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
      IntervalLp 𝕜 operatorReductionL1Exponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (j : Fin S.card) :
    (∑ i : Fin S.card,
      ‖operatorReductionPacketMatrix operatorReductionL1Exponent Q n S i j‖) ≤ ‖Q‖ := by
  let y := Q (lpHaarNormalizedVector 𝕜 operatorReductionL1Exponent
    (some ⟨n, S.orderEmbOfFin rfl j⟩))
  change (∑ i : Fin S.card, ‖lpHaarNormalizedCoordinate 𝕜 operatorReductionL1Exponent
    (some ⟨n, S.orderEmbOfFin rfl i⟩) y‖) ≤ _
  rw [packetMatrix_sum_index n S (fun k =>
    ‖lpHaarNormalizedCoordinate 𝕜 operatorReductionL1Exponent (some ⟨n, k⟩) y‖)]
  calc
    _ ≤ ‖y‖ := innerMatrixNormalizedCoordinate_sum_le n S y
    _ ≤ ‖Q‖ * ‖lpHaarNormalizedVector 𝕜 operatorReductionL1Exponent
        (some ⟨n, S.orderEmbOfFin rfl j⟩)‖ := Q.le_opNorm _
    _ = _ := by
      rw [lpHaarNormalizedVector_norm 𝕜 operatorReductionL1Exponent
        (by norm_num [operatorReductionL1Exponent]), mul_one]

theorem operatorReductionInnerMatrix_entry_norm_le
    (Q : IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
      IntervalLp 𝕜 operatorReductionL1Exponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (i j : Fin S.card) :
    ‖operatorReductionPacketMatrix operatorReductionL1Exponent Q n S i j‖ ≤ ‖Q‖ := by
  exact (Finset.single_le_sum (f := fun i : Fin S.card =>
    ‖operatorReductionPacketMatrix operatorReductionL1Exponent Q n S i j‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans
    (operatorReductionInnerMatrix_column_sum_le Q n S j)

theorem operatorReductionInnerMatrix_column_square_sum_le
    (Q : IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
      IntervalLp 𝕜 operatorReductionL1Exponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (j : Fin S.card) :
    (∑ i : Fin S.card,
      ‖operatorReductionPacketMatrix operatorReductionL1Exponent Q n S i j‖ ^ 2) ≤
        ‖Q‖ ^ 2 := by
  calc
    _ ≤ ∑ i : Fin S.card, ‖Q‖ *
        ‖operatorReductionPacketMatrix operatorReductionL1Exponent Q n S i j‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [pow_two] using mul_le_mul_of_nonneg_right
        (operatorReductionInnerMatrix_entry_norm_le Q n S i j) (norm_nonneg _)
    _ = ‖Q‖ * ∑ i : Fin S.card,
        ‖operatorReductionPacketMatrix operatorReductionL1Exponent Q n S i j‖ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ‖Q‖ * ‖Q‖ := mul_le_mul_of_nonneg_left
      (operatorReductionInnerMatrix_column_sum_le Q n S j) (norm_nonneg _)
    _ = _ := (pow_two _).symm

theorem operatorReductionInnerMatrix_square_sum_le
    (Q : IntervalLp 𝕜 operatorReductionL1Exponent →L[𝕜]
      IntervalLp 𝕜 operatorReductionL1Exponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    (∑ i : Fin S.card, ∑ j : Fin S.card,
      ‖operatorReductionPacketMatrix operatorReductionL1Exponent Q n S i j‖ ^ 2) ≤
        (S.card : ℝ) * ‖Q‖ ^ 2 := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _j : Fin S.card, ‖Q‖ ^ 2 :=
      Finset.sum_le_sum (fun j _ => operatorReductionInnerMatrix_column_square_sum_le Q n S j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]

end SurveyStatements.P5OperatorReduction
