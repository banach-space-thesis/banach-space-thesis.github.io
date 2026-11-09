import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The time-face cofactor of an augmented Jacobian

The last coordinate is time. The final output coordinate is time itself, so
the augmented Jacobian has last row `[0,...,0,1]`. Its bottom-right adjugate
entry is exactly the spatial Jacobian determinant, independently of the
time-derivative column.
-/

namespace BanachIsometric

def augmentedJacobian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Fin.snoc (fun i : Fin n ↦ Fin.snoc (A i) (b i)) (Pi.single (Fin.last n) 1)

@[simp]
theorem snoc_block_spatial_minor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (r : Fin (n + 1) → ℝ) :
    Matrix.submatrix (Fin.snoc (fun i : Fin n ↦ Fin.snoc (A i) (b i)) r)
      Fin.castSucc Fin.castSucc = A := by
  ext i j
  simp [Matrix.submatrix_apply]

/-- The corner cofactor ignores both the last column and the last row. This
also applies to the rank-deficient lift with constant final coordinate. -/
theorem adjugate_snoc_block_last_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (r : Fin (n + 1) → ℝ) :
    Matrix.adjugate (Fin.snoc (fun i : Fin n ↦ Fin.snoc (A i) (b i)) r)
      (Fin.last n) (Fin.last n) = A.det := by
  have hsign : (-1 : ℝ) ^ (n + n) = 1 := by
    calc
      (-1 : ℝ) ^ (n + n) = ((-1 : ℝ) * (-1)) ^ n := by rw [pow_add, mul_pow]
      _ = 1 := by simp
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_last, Fin.succAbove_last, snoc_block_spatial_minor, hsign, one_mul]

@[simp]
theorem augmentedJacobian_spatial_minor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (augmentedJacobian A b).submatrix Fin.castSucc Fin.castSucc = A := by
  ext i j
  simp [augmentedJacobian, Matrix.submatrix_apply]

theorem adjugate_augmentedJacobian_last_last {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (augmentedJacobian A b).adjugate (Fin.last n) (Fin.last n) = A.det :=
  adjugate_snoc_block_last_last A b (Pi.single (Fin.last n) 1)

end BanachIsometric
