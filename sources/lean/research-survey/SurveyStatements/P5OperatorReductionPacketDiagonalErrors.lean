import SurveyStatements.P5OperatorReductionPacketMatrixRaw
import SurveyStatements.P5OperatorReductionSignIdentity
import SurveyStatements.P5Support.LpHaarBlockReaders

/-! Exact pointwise signed-block diagonal errors for actual scalar
operators, expressed by the same raw matrix used in the moment bounds. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal Classical BigOperators

namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem operatorReductionSignedBlockReader_eq_quadratic
    (p : BanachExponent) (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    lpHaarSignedBlockReader 𝕜 p n S θ (Q (lpHaarSignedBlock 𝕜 p n S θ)) =
      (S.card : 𝕜)⁻¹ * ∑ k ∈ S, ∑ l ∈ S,
        scalarSign (θ k) * scalarSign (θ l) *
          lpHaarDyadicCoefficient 𝕜 p n k (Q (lpHaarDyadic 𝕜 p n l)) := by
  rw [lpHaarSignedBlockReader_apply, lpHaarSignedBlock, map_sum]
  simp_rw [map_sum, signedValue_sum]
  apply congrArg (fun z : 𝕜 => (S.card : 𝕜)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [map_signedValue, map_signedValue, ← scalarSign_mul, ← scalarSign_mul]
  ring

theorem operatorReductionRawPacketMatrix_quadratic_eq_block_sum
    (p : BanachExponent) (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    (∑ i : Fin S.card, ∑ j : Fin S.card,
      scalarSign (θ (S.orderEmbOfFin rfl i)) * scalarSign (θ (S.orderEmbOfFin rfl j)) *
        operatorReductionRawPacketMatrix p Q n S i j) =
      ∑ k ∈ S, ∑ l ∈ S, scalarSign (θ k) * scalarSign (θ l) *
        lpHaarDyadicCoefficient 𝕜 p n k (Q (lpHaarDyadic 𝕜 p n l)) := by
  unfold operatorReductionRawPacketMatrix
  calc
    _ = ∑ i : Fin S.card, ∑ l ∈ S,
        scalarSign (θ (S.orderEmbOfFin rfl i)) * scalarSign (θ l) *
          lpHaarDyadicCoefficient 𝕜 p n (S.orderEmbOfFin rfl i)
            (Q (lpHaarDyadic 𝕜 p n l)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact packetMatrix_sum_index n S (fun l =>
        scalarSign (θ (S.orderEmbOfFin rfl i)) * scalarSign (θ l) *
          lpHaarDyadicCoefficient 𝕜 p n (S.orderEmbOfFin rfl i)
            (Q (lpHaarDyadic 𝕜 p n l)))
    _ = _ := packetMatrix_sum_index n S (fun k => ∑ l ∈ S,
      scalarSign (θ k) * scalarSign (θ l) *
        lpHaarDyadicCoefficient 𝕜 p n k (Q (lpHaarDyadic 𝕜 p n l)))

theorem operatorReductionRawPacketMatrix_diagonal_eq_block_sum
    (p : BanachExponent) (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    (∑ i : Fin S.card, operatorReductionRawPacketMatrix p Q n S i i) =
      ∑ k ∈ S, lpHaarDyadicCoefficient 𝕜 p n k (Q (lpHaarDyadic 𝕜 p n k)) :=
  packetMatrix_sum_index n S (fun k =>
    lpHaarDyadicCoefficient 𝕜 p n k (Q (lpHaarDyadic 𝕜 p n k)))

/-- No nonemptiness or exponent hypothesis is needed for this exact
algebraic identity; the moment estimates add their own analytic hypotheses. -/
theorem operatorReductionSignedBlock_diagonal_error_eq_centered
    (p : BanachExponent) (Q : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    lpHaarSignedBlockReader 𝕜 p n S θ (Q (lpHaarSignedBlock 𝕜 p n S θ)) -
      (S.card : 𝕜)⁻¹ *
        ∑ k ∈ S, lpHaarDyadicCoefficient 𝕜 p n k (Q (lpHaarDyadic 𝕜 p n k)) =
      (S.card : 𝕜)⁻¹ * centeredQuadraticForm (operatorReductionRawPacketMatrix p Q n S)
        (fun i => θ (S.orderEmbOfFin rfl i)) := by
  rw [operatorReductionSignedBlockReader_eq_quadratic p Q n S θ,
    centeredQuadraticForm_eq_diagonal_error,
    operatorReductionRawPacketMatrix_quadratic_eq_block_sum p Q n S θ,
    operatorReductionRawPacketMatrix_diagonal_eq_block_sum p Q n S, mul_sub]

end SurveyStatements.P5OperatorReduction
