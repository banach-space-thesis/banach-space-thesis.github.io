import BanachIsometric.SignedSimplexFaceGeometry

/-! The centered facet vertices and the oriented facet chart have the
same determinant. The first vertex and the successive vertex differences
are replaced by the actual vertex columns through a determinant-one matrix. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Matrix

def signedFacetVertexMatrix (n : ℕ) (i : Fin (n + 2)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun row col => (Pi.single (i.succAbove col) (1 : ℝ) : Fin (n + 2) → ℝ) row.succ - signedFacetCenter n

private theorem insertNth_single (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    Fin.insertNth (α := fun _ => ℝ) i 0 (Pi.single j 1) = Pi.single (i.succAbove j) 1 := by
  funext k
  refine Fin.succAboveCases i ?_ (fun l => ?_) k
  · simp
  · simp [Pi.single_apply]

private theorem barycentric_zero (n : ℕ) :
    signedSimplexBarycentric n 0 = Pi.single (0 : Fin (n + 1)) 1 := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · simp

private theorem barycentric_single (n : ℕ) (j : Fin n) :
    signedSimplexBarycentric n (Pi.single j 1) = Pi.single j.succ 1 := by
  funext k
  refine Fin.cases ?_ (fun l => ?_) k
  · simp [Pi.single_apply, eq_comm]
  · simp [Pi.single_apply]

private def facetColumnAddition (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of (Fin.cons (fun _ => 1) (fun k => Fin.cons 0 (Pi.single k 1)))

private theorem facetColumnAddition_det (n : ℕ) : (facetColumnAddition n).det = 1 := by
  have hminor : (facetColumnAddition n).submatrix Fin.succ Fin.succ = 1 := by
    ext i j
    simp [facetColumnAddition, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, hminor, Matrix.det_one]
  simp [facetColumnAddition]

private theorem signedFacetVertexMatrix_eq_mul (n : ℕ) (i : Fin (n + 2)) :
    signedFacetVertexMatrix n i = signedFacetChartMatrix n i 0 * facetColumnAddition n := by
  ext row col
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun j => ?_) col
  · have h := signedFacetVector_apply n i 0 row
    rw [barycentric_zero, insertNth_single] at h
    simpa [signedFacetVertexMatrix, facetColumnAddition, signedFacetVector] using h.symm
  · have h := congrArg (fun x : Fin (n + 1) → ℝ => x row)
      (signedFacetVector_affine n i (Pi.single j 1))
    change signedFacetVector n i (Pi.single j 1) row =
      signedFacetVector n i 0 row + signedFacetSlope n i (Pi.single j 1) row at h
    rw [signedFacetVector_apply n i (Pi.single j 1), barycentric_single, insertNth_single,
      ← signedFacetChartMatrix_succ n i 0] at h
    simpa [signedFacetVertexMatrix, facetColumnAddition, signedFacetVector, Pi.single_apply, eq_comm] using h

theorem signedFacetVertexMatrix_det (n : ℕ) (i : Fin (n + 2)) :
    (signedFacetVertexMatrix n i).det = Int.negOnePow (i.val : ℤ) • signedFacetCenter n := by
  rw [signedFacetVertexMatrix_eq_mul, Matrix.det_mul, facetColumnAddition_det, mul_one, signedFacetChartMatrix_det]

def signedHemisphereVertexMatrix (n : ℕ) (ε : ℝ) (i : Fin (n + 2)) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  Matrix.of (Fin.cons (Fin.cons ε 0) (fun row => Fin.cons 0 (signedFacetVertexMatrix n i row)))

theorem signedHemisphereVertexMatrix_det (n : ℕ) (ε : ℝ) (i : Fin (n + 2)) :
    (signedHemisphereVertexMatrix n ε i).det = ε * (Int.negOnePow (i.val : ℤ) • signedFacetCenter n) := by
  have hminor : (signedHemisphereVertexMatrix n ε i).submatrix Fin.succ Fin.succ = signedFacetVertexMatrix n i := by
    ext row col
    rfl
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, hminor, signedFacetVertexMatrix_det]
  simp [signedHemisphereVertexMatrix]

end BanachIsometric.SingularPrism
