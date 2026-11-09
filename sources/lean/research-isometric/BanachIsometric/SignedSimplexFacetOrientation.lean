import BanachIsometric.SignedSimplexCoordinates
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

/-! The determinant of an oriented radial facet chart. In barycentric
coordinates the full rectangular matrix has zero column sums. Deleting the
first row rather than the omitted vertex therefore changes the determinant by
the alternating sign of that vertex. This is the sign in the singular boundary. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Matrix

def signedFacetCenter (n : ℕ) : ℝ := 1 / (n + 2 : ℕ)

theorem signedFacetCenter_pos (n : ℕ) : 0 < signedFacetCenter n := by
  unfold signedFacetCenter
  positivity

def signedSimplexDirection (n : ℕ) (v : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (-∑ j, v j) v

theorem signedSimplexDirection_sum (n : ℕ) (v : Fin n → ℝ) :
    ∑ j, signedSimplexDirection n v j = 0 := by
  rw [Fin.sum_univ_succ]
  simp [signedSimplexDirection]

theorem signedSimplexBarycentric_sum (n : ℕ) (x : Fin n → ℝ) :
    ∑ j, signedSimplexBarycentric n x j = 1 := by
  rw [Fin.sum_univ_succ]
  simp

theorem signedFacetCenter_mul (n : ℕ) : ((n + 2 : ℕ) : ℝ) * signedFacetCenter n = 1 := by
  have h : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  exact mul_one_div_cancel h

def signedFacetFullMatrix (n : ℕ) (i : Fin (n + 2)) (x : Fin n → ℝ) :
    Matrix (Fin (n + 2)) (Fin (n + 1)) ℝ :=
  Matrix.of fun row => Fin.cons
    (Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) (signedSimplexBarycentric n x) row - signedFacetCenter n)
    (fun col => Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) (signedSimplexDirection n (Pi.single col 1)) row)

@[simp] theorem signedFacetFullMatrix_col_zero (n : ℕ) (i : Fin (n + 2))
    (x : Fin n → ℝ) (row : Fin (n + 2)) :
    signedFacetFullMatrix n i x row 0 =
      Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) (signedSimplexBarycentric n x) row - signedFacetCenter n := rfl

@[simp] theorem signedFacetFullMatrix_col_succ (n : ℕ) (i : Fin (n + 2))
    (x : Fin n → ℝ) (row : Fin (n + 2)) (col : Fin n) :
    signedFacetFullMatrix n i x row col.succ =
      Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) (signedSimplexDirection n (Pi.single col 1)) row := rfl

theorem signedFacetFullMatrix_sum (n : ℕ) (i : Fin (n + 2)) (x : Fin n → ℝ) :
    ∑ row, signedFacetFullMatrix n i x row = 0 := by
  funext col
  rw [Finset.sum_apply, Pi.zero_apply]
  refine Fin.cases ?_ (fun j => ?_) col
  · simp only [signedFacetFullMatrix_col_zero, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, signedFacetCenter_mul]
    rw [Fin.sum_univ_succAbove _ i]
    simp [signedSimplexBarycentric_sum]
  · simp only [signedFacetFullMatrix_col_succ]
    rw [Fin.sum_univ_succAbove _ i]
    simp [signedSimplexDirection_sum]

theorem signedFacetFullMatrix_det_drop_facet (n : ℕ) (i : Fin (n + 2)) (x : Fin n → ℝ) :
    ((signedFacetFullMatrix n i x).submatrix i.succAbove id).det = signedFacetCenter n := by
  let A := (signedFacetFullMatrix n i x).submatrix i.succAbove id
  change A.det = signedFacetCenter n
  have hsum : ∑ row, A row 0 = signedFacetCenter n := by
    dsimp only [A, Matrix.submatrix_apply, id_eq]
    simp only [signedFacetFullMatrix_col_zero, Fin.insertNth_apply_succAbove,
      Finset.sum_sub_distrib, signedSimplexBarycentric_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h := signedFacetCenter_mul n
    push_cast at h ⊢
    linarith
  have hminor : A.submatrix Fin.succ Fin.succ = 1 := by
    ext row col
    simp [A, signedSimplexDirection, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [Matrix.det_eq_sum_column_mul_submatrix_succAbove_succAbove_det A 0 0]
  · simp [hsum, hminor]
  · intro col hcol
    refine Fin.cases (fun h => (h rfl).elim) (fun j _ => ?_) col hcol
    simp [A, signedSimplexDirection_sum]

def signedFacetChartMatrix (n : ℕ) (i : Fin (n + 2)) (x : Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (signedFacetFullMatrix n i x).submatrix (0 : Fin (n + 2)).succAbove id

theorem signedFacetChartMatrix_det (n : ℕ) (i : Fin (n + 2)) (x : Fin n → ℝ) :
    (signedFacetChartMatrix n i x).det = Int.negOnePow (i.val : ℤ) • signedFacetCenter n := by
  unfold signedFacetChartMatrix
  rw [Matrix.submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det
    _ (signedFacetFullMatrix_sum n i x) 0 i, signedFacetFullMatrix_det_drop_facet]
  simp

end BanachIsometric.SingularPrism
