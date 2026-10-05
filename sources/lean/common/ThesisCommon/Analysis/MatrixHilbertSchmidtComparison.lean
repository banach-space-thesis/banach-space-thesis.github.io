import ThesisCommon.Analysis.MatrixExponentChange
import ThesisCommon.Analysis.MatrixHilbertSchmidtBounds

/-! The printed Hilbert--Schmidt/operator norm comparison for finite lp
matrices. The change of exponent preserves every scalar matrix entry. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem matrixExponentDeviation_lt_half (p : BanachExponent)
    (hp : 1 < p.val.toReal) : |1 / p.val.toReal - 1 / 2| < 1 / 2 := by
  have hp0 : 0 < p.val.toReal := zero_lt_one.trans hp
  have hi0 : 0 < 1 / p.val.toReal := one_div_pos.mpr hp0
  have hi1 : 1 / p.val.toReal < 1 := (div_lt_one hp0).mpr hp
  rw [abs_lt]
  constructor <;> linarith

theorem matrixHilbertSchmidtNorm_le_dimension_mul_norm (p : BanachExponent)
    (hp : p.val ≠ ∞) {N : ℕ} (hN : 0 < N) (A : FiniteMatrixBlock 𝕜 p N) :
    matrixHilbertSchmidtNorm p A ≤
      (N : ℝ) ^ (1 / 2 + |1 / p.val.toReal - 1 / 2|) * ‖A‖ := by
  have h2 : matrixHilbertExponent.val ≠ ∞ := by norm_num [matrixHilbertExponent]
  let B := matrixExponentChange p matrixHilbertExponent hp h2 A
  have hB : ‖B‖ ≤ (N : ℝ) ^ |1 / p.val.toReal - 1 / 2| * ‖A‖ := by
    simpa only [matrixHilbertExponent_val, ENNReal.toReal_ofNat] using
      norm_matrixExponentChange_le p matrixHilbertExponent hp h2 hN A
  calc
    matrixHilbertSchmidtNorm p A = matrixHilbertSchmidtNorm matrixHilbertExponent B :=
      (matrixHilbertSchmidtNorm_exponentChange p matrixHilbertExponent hp h2 A).symm
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) * ‖B‖ := matrixHilbertSchmidtNorm_le_rpow_mul_norm B
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) * ((N : ℝ) ^ |1 / p.val.toReal - 1 / 2| * ‖A‖) :=
      mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [← mul_assoc, ← Real.rpow_add (Nat.cast_pos.mpr hN)]

theorem norm_le_dimension_mul_matrixHilbertSchmidtNorm (p : BanachExponent)
    (hp : p.val ≠ ∞) {N : ℕ} (hN : 0 < N) (A : FiniteMatrixBlock 𝕜 p N) :
    ‖A‖ ≤ (N : ℝ) ^ |1 / p.val.toReal - 1 / 2| * matrixHilbertSchmidtNorm p A := by
  have h2 : matrixHilbertExponent.val ≠ ∞ := by norm_num [matrixHilbertExponent]
  let B := matrixExponentChange p matrixHilbertExponent hp h2 A
  have hA := norm_matrixExponentChange_le matrixHilbertExponent p h2 hp hN B
  have hAB : matrixExponentChange matrixHilbertExponent p h2 hp B = A :=
    matrixExponentChange_inverse p matrixHilbertExponent hp h2 A
  rw [hAB] at hA
  have hA' : ‖A‖ ≤ (N : ℝ) ^ |1 / p.val.toReal - 1 / 2| * ‖B‖ := by
    simpa only [matrixHilbertExponent_val, ENNReal.toReal_ofNat, abs_sub_comm] using hA
  calc
    ‖A‖ ≤ (N : ℝ) ^ |1 / p.val.toReal - 1 / 2| * ‖B‖ := hA'
    _ ≤ (N : ℝ) ^ |1 / p.val.toReal - 1 / 2| * matrixHilbertSchmidtNorm matrixHilbertExponent B :=
      mul_le_mul_of_nonneg_left (norm_le_matrixHilbertSchmidtNorm B)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [matrixHilbertSchmidtNorm_exponentChange]

end ThesisCommon
