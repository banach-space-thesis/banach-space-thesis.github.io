import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The printed geometric control sequence, with coordinate k representing
the manuscript's block k+1. -/
noncomputable section
namespace ThesisCommon

def matrixGeometricControl (ε K : ℝ) (k : ℕ) : ℝ :=
  ε / (2 ^ (k + 4) * (1 + K))

theorem matrixGeometricControl_pos {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) (k : ℕ) :
    0 < matrixGeometricControl ε K k :=
  div_pos hε (mul_pos (pow_pos (by norm_num) _) (by linarith))

theorem matrixGeometricControl_mul_le {ε K : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K) (k : ℕ) :
    matrixGeometricControl ε K k * (1 + K) ≤ ε / 16 := by
  have hKpos : 0 < 1 + K := by linarith
  have heq : matrixGeometricControl ε K k * (1 + K) = ε / 2 ^ (k + 4) := by
    unfold matrixGeometricControl
    field_simp
  rw [heq]
  have hpow : (16 : ℝ) ≤ 2 ^ (k + 4) := by
    calc
      (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
      _ ≤ 2 ^ (k + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact div_le_div_of_nonneg_left hε (by norm_num) hpow

end ThesisCommon
