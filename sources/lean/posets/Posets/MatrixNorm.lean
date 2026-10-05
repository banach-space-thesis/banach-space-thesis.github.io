import Posets.MatrixOperators
import Mathlib.Analysis.RCLike.Lemmas

noncomputable section
open scoped BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]

def normingPhase (z : 𝕜) : 𝕜 := starRingEnd 𝕜 z / (‖z‖ : 𝕜)

theorem norm_normingPhase_le (z : 𝕜) : ‖normingPhase z‖ ≤ 1 := by
  simp only [normingPhase, norm_div, RCLike.norm_conj, RCLike.norm_ofReal,
    abs_norm]
  by_cases hz : z = 0
  · simp [hz]
  · simp [norm_ne_zero_iff.mpr hz]

theorem mul_normingPhase (z : 𝕜) : z * normingPhase z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [hz, normingPhase]
  · have hn : (‖z‖ : 𝕜) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    simp only [normingPhase, ← mul_div_assoc, RCLike.mul_conj, pow_two,
      mul_div_cancel_right₀ _ hn]

/-- A bounded scalar sequence that norms the selected matrix row. -/
def normingRow (M : ScalarMatrix 𝕜) (k : ℕ) : ℕ →ᵇ 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => normingPhase (M k n))
    1 (fun n => norm_normingPhase_le (M k n))

theorem norm_normingRow_le (M : ScalarMatrix 𝕜) (k : ℕ) : ‖normingRow M k‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le zero_le_one).mpr (fun n => norm_normingPhase_le (M k n))

/-- The matrix row-sum norm equals the genuine operator norm on ℓ∞. -/
theorem norm_matrixOperator (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M) :
    ‖matrixOperator M hM‖ = matrixNorm 𝕜 M := by
  apply le_antisymm (norm_matrixOperator_le M hM)
  apply ciSup_le
  intro k
  have heval : matrixOperator M hM (normingRow M k) k =
      ((∑' n, ‖M k n‖ : ℝ) : 𝕜) := by
    change (∑' n, M k n * normingPhase (M k n)) = _
    simp_rw [mul_normingPhase]
    exact ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).map_tsum (hM.1 k)).symm
  calc
    (∑' n, ‖M k n‖) = ‖matrixOperator M hM (normingRow M k) k‖ := by
      rw [heval, RCLike.norm_ofReal, abs_of_nonneg (tsum_nonneg (fun n => norm_nonneg _))]
    _ ≤ ‖matrixOperator M hM (normingRow M k)‖ :=
      (matrixOperator M hM (normingRow M k)).norm_coe_le_norm k
    _ ≤ ‖matrixOperator M hM‖ * ‖normingRow M k‖ :=
      (matrixOperator M hM).le_opNorm _
    _ ≤ ‖matrixOperator M hM‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_normingRow_le M k) (norm_nonneg _)
    _ = ‖matrixOperator M hM‖ := mul_one _

end Posets
