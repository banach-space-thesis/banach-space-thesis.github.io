import JLMS.Definitions
import Mathlib.Tactic

/-!
# Pairing a nearly diagonal matrix

Half-differences of rows and opposite-sign pairs of columns keep the average
of the two original diagonal entries as the main diagonal. If each original
off-diagonal column in pair j is bounded by w_j, every error coefficient of
the paired matrix is bounded by 2w_j, including its diagonal error.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]

def pairedMatrixCoefficient (A : ℕ → ℕ → 𝕜) (i j : ℕ) : 𝕜 :=
  ((1 / 2 : ℝ) : 𝕜) * (A (2 * i) (2 * j) - A (2 * i) (2 * j + 1) -
    A (2 * i + 1) (2 * j) + A (2 * i + 1) (2 * j + 1))

def pairedDiagonalCoefficient (A : ℕ → ℕ → 𝕜) (i : ℕ) : 𝕜 :=
  ((1 / 2 : ℝ) : 𝕜) * (A (2 * i) (2 * i) + A (2 * i + 1) (2 * i + 1))

theorem norm_pairedMatrix_error_le (A : ℕ → ℕ → 𝕜) (w : ℕ → ℝ)
    (hw : ∀ j, 0 ≤ w j)
    (hoff : ∀ i j, i ≠ j → ‖A i j‖ ≤ w (j / 2)) (i j : ℕ) :
    ‖pairedMatrixCoefficient A i j - (if j = i then pairedDiagonalCoefficient A i else 0)‖ ≤
      2 * w j := by
  have hh : ‖((1 / 2 : ℝ) : 𝕜)‖ = 1 / 2 := by rw [RCLike.norm_ofReal]; norm_num
  have heven : (2 * j) / 2 = j := by omega
  have hodd : (2 * j + 1) / 2 = j := by omega
  by_cases hji : j = i
  · subst j
    have heq : pairedMatrixCoefficient A i i - pairedDiagonalCoefficient A i =
        ((1 / 2 : ℝ) : 𝕜) * (-A (2 * i) (2 * i + 1) - A (2 * i + 1) (2 * i)) := by
      dsimp [pairedMatrixCoefficient, pairedDiagonalCoefficient]
      ring
    simp only [ite_true]
    rw [heq, norm_mul, hh]
    have ha := hoff (2 * i) (2 * i + 1) (by omega)
    have hb := hoff (2 * i + 1) (2 * i) (by omega)
    rw [hodd] at ha
    rw [heven] at hb
    have h := norm_sub_le (-A (2 * i) (2 * i + 1)) (A (2 * i + 1) (2 * i))
    rw [norm_neg] at h
    nlinarith [hw i]
  · have hij : i ≠ j := Ne.symm hji
    have ha := hoff (2 * i) (2 * j) (by omega)
    have hb := hoff (2 * i) (2 * j + 1) (by omega)
    have hc := hoff (2 * i + 1) (2 * j) (by omega)
    have hd := hoff (2 * i + 1) (2 * j + 1) (by omega)
    rw [heven] at ha hc
    rw [hodd] at hb hd
    rw [if_neg hji, sub_zero, pairedMatrixCoefficient, norm_mul, hh]
    have h₁ := norm_sub_le (A (2 * i) (2 * j)) (A (2 * i) (2 * j + 1))
    have h₂ := norm_sub_le (A (2 * i) (2 * j) - A (2 * i) (2 * j + 1))
      (A (2 * i + 1) (2 * j))
    have h₃ := norm_add_le
      (A (2 * i) (2 * j) - A (2 * i) (2 * j + 1) - A (2 * i + 1) (2 * j))
      (A (2 * i + 1) (2 * j + 1))
    linarith

end JLMS
