import SurveyStatements.P5OperatorReductionPacketMatrixPhases
import SurveyStatements.P5OperatorReductionPacketGeometryNorms

/-! Genuine row ℓ₁ estimates from bounded operator norm and actual disjoint
same-level Haar packet geometry. No matrix sparsity or structural assumption is used. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical ENNReal

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

theorem packetMatrix_normalizedHaar_row_sum_le
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (i : Option LpHaarTreeIndex) :
    (∑ k ∈ S, ‖lpHaarNormalizedCoordinate 𝕜 p i
      (Q (lpHaarNormalizedVector 𝕜 p (some ⟨n, k⟩)))‖) ≤
        6 * ‖Q‖ * (S.card : ℝ) ^ (1 / p.val.toReal) := by
  let a : Fin (2 ^ n) → 𝕜 := fun k =>
    lpHaarNormalizedCoordinate 𝕜 p i (Q (lpHaarNormalizedVector 𝕜 p (some ⟨n, k⟩)))
  let b : Fin (2 ^ n) → 𝕜 := fun k => packetMatrixNormingPhase (a k)
  have hb : ∀ k ∈ S, ‖b k‖ ≤ 1 := fun k _ => packetMatrixNormingPhase_norm_le (a k)
  have hnorm : ‖operatorReductionNormalizedHaarPacket 𝕜 p n S b‖ ≤
      (S.card : ℝ) ^ (1 / p.val.toReal) :=
    norm_operatorReductionNormalizedHaarPacket_le p hp n S b hb
  have heval : lpHaarNormalizedCoordinate 𝕜 p i
      (Q (operatorReductionNormalizedHaarPacket 𝕜 p n S b)) =
        ∑ k ∈ S, b k * a k := by
    simp only [operatorReductionNormalizedHaarPacket, map_sum, map_smul,
      smul_eq_mul, a]
  have hmass : ‖lpHaarNormalizedCoordinate 𝕜 p i
      (Q (operatorReductionNormalizedHaarPacket 𝕜 p n S b))‖ = ∑ k ∈ S, ‖a k‖ := by
    rw [heval]
    exact packetMatrixNormingPhase_sum_norm S a
  change (∑ k ∈ S, ‖a k‖) ≤ _
  rw [← hmass]
  calc
    _ ≤ ‖lpHaarNormalizedCoordinate 𝕜 p i‖ *
        ‖Q (operatorReductionNormalizedHaarPacket 𝕜 p n S b)‖ :=
      (lpHaarNormalizedCoordinate 𝕜 p i).le_opNorm _
    _ ≤ 6 * (‖Q‖ * ‖operatorReductionNormalizedHaarPacket 𝕜 p n S b‖) :=
      mul_le_mul (packetMatrix_normalizedCoordinate_norm_le p hp i) (Q.le_opNorm _)
        (norm_nonneg _) (by norm_num)
    _ ≤ 6 * (‖Q‖ * (S.card : ℝ) ^ (1 / p.val.toReal)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
        (by norm_num)
    _ = _ := by ring

theorem operatorReductionPacketMatrix_row_sum_le
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (i : Fin S.card) :
    (∑ j : Fin S.card, ‖operatorReductionPacketMatrix p Q n S i j‖) ≤
      6 * ‖Q‖ * (S.card : ℝ) ^ (1 / p.val.toReal) := by
  unfold operatorReductionPacketMatrix
  rw [packetMatrix_sum_index n S (fun k =>
    ‖lpHaarNormalizedCoordinate 𝕜 p (some ⟨n, S.orderEmbOfFin rfl i⟩)
      (Q (lpHaarNormalizedVector 𝕜 p (some ⟨n, k⟩)))‖)]
  exact packetMatrix_normalizedHaar_row_sum_le p hp Q n S _

end SurveyStatements.P5OperatorReduction
