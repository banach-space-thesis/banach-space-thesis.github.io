import ThesisCommon.Analysis.MatrixAlmostDiagonalVectors

/-! The finite past and full tail estimates give an operator-norm bound
for compression minus the genuine coordinatewise diagonal. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent}
variable {T : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p} {b : ℕ → ℝ}
namespace MatrixAlmostDiagonalData
variable (d : MatrixAlmostDiagonalData p T b)
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

private theorem restrict_norm_le_projection (k : ℕ)
    (z : FiniteMatrixBlock 𝕜 p (d.n k + 1)) :
    ‖matrixRestrict p (d.row k).toEmbedding (d.col k).toEmbedding z‖ ≤
      ‖matrixBlockProjection p (d.row k).toEmbedding (d.col k).toEmbedding z‖ := by
  let S := matrixRestrict (𝕜 := 𝕜) p (d.row k).toEmbedding (d.col k).toEmbedding
  let Q := matrixBlockProjection (𝕜 := 𝕜) p (d.row k).toEmbedding (d.col k).toEmbedding
  have heq : S (Q z) = S z :=
    DFunLike.congr_fun (matrixRestrict_comp_insert p (d.row k).toEmbedding (d.col k).toEmbedding) (S z)
  calc
    ‖S z‖ = ‖S (Q z)‖ := congrArg norm heq.symm
    _ ≤ ‖S‖ * ‖Q z‖ := S.le_opNorm _
    _ ≤ 1 * ‖Q z‖ := mul_le_mul_of_nonneg_right (norm_matrixRestrict_le (𝕜 := 𝕜) p _ _) (norm_nonneg _)
    _ = ‖Q z‖ := one_mul _

theorem past_error_le (hb : ∀ k, 0 ≤ b k) (x : FiniteMatrixSum 𝕜 p) (k : ℕ) :
    ‖matrixRestrict p (d.row k).toEmbedding (d.col k).toEmbedding
      (T (d.insert (matrixSumMask p (Set.Iio k) x)) (d.n k))‖ ≤ b k * ‖T‖ * ‖x‖ := by
  let y := d.insert (matrixSumMask p (Set.Iio k) x)
  have hy : y ∈ d.past k := d.insert_past_mem x k
  have hynorm : ‖y‖ ≤ ‖x‖ := d.norm_insert_mask_le _ x
  calc
    _ ≤ ‖matrixBlockProjection p (d.row k).toEmbedding (d.col k).toEmbedding (T y (d.n k))‖ :=
      d.restrict_norm_le_projection k _
    _ ≤ b k * ‖T y (d.n k)‖ := d.past_small k y hy
    _ ≤ b k * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left
      ((lp.norm_apply_le_norm ENNReal.top_ne_zero (T y) _).trans
        ((T.le_opNorm y).trans (mul_le_mul_of_nonneg_left hynorm (norm_nonneg T)))) (hb k)
    _ = _ := (mul_assoc _ _ _).symm

theorem future_error_le (hb : ∀ k, 0 ≤ b k) (x : FiniteMatrixSum 𝕜 p) (k : ℕ) :
    ‖matrixRestrict p (d.row k).toEmbedding (d.col k).toEmbedding
      (T (d.insert (matrixSumMask p (Set.Ioi k) x)) (d.n k))‖ ≤ b k * ‖x‖ := by
  let y := d.insert (matrixSumMask p (Set.Ioi k) x)
  let R := ((matrixSumCoordinate (𝕜 := 𝕜) p (d.n k)).comp T).comp
    (matrixSumMask p (d.band (k + 1)))
  have heq : R y = T y (d.n k) := by
    change T (matrixSumMask p (d.band (k + 1)) y) (d.n k) = T y (d.n k)
    rw [d.insert_tail_band]
  have hRy : ‖T y (d.n k)‖ ≤ b k * ‖x‖ := by
    rw [← heq]
    exact (R.le_opNorm y).trans (mul_le_mul (d.future_small k)
      (d.norm_insert_mask_le _ x) (norm_nonneg y) (hb k))
  exact ((matrixRestrict (𝕜 := 𝕜) p (d.row k).toEmbedding (d.col k).toEmbedding).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (norm_matrixRestrict_le (𝕜 := 𝕜) p _ _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hRy))

theorem coordinate_error_le (hb : ∀ k, 0 ≤ b k) (x : FiniteMatrixSum 𝕜 p) (k : ℕ) :
    ‖(((d.read.comp T).comp d.insert - d.diagonal) x) k‖ ≤
      (b k * (1 + ‖T‖)) * ‖x‖ := by
  let S := matrixRestrict (𝕜 := 𝕜) p (d.row k).toEmbedding (d.col k).toEmbedding
  have hsplit := congrArg (fun z : FiniteMatrixSum 𝕜 p => S (T (d.insert z) (d.n k)))
    (matrixSum_past_single_tail x k)
  simp only [map_add, lp.coeFn_add, Pi.add_apply] at hsplit
  have heq : (((d.read.comp T).comp d.insert - d.diagonal) x) k =
      S (T (d.insert (matrixSumMask p (Set.Iio k) x)) (d.n k)) +
      S (T (d.insert (matrixSumMask p (Set.Ioi k) x)) (d.n k)) := by
    change S (T (d.insert x) (d.n k)) - d.diagonalEntry k (x k) = _
    rw [d.diagonalEntry_apply, hsplit]
    change (_ + S (T (d.insert (matrixSumSingle p k (x k))) (d.n k)) + _) -
      S (T (d.insert (matrixSumSingle p k (x k))) (d.n k)) = _
    abel
  rw [heq]
  calc
    _ ≤ ‖S (T (d.insert (matrixSumMask p (Set.Iio k) x)) (d.n k))‖ +
        ‖S (T (d.insert (matrixSumMask p (Set.Ioi k) x)) (d.n k))‖ := norm_add_le _ _
    _ ≤ b k * ‖T‖ * ‖x‖ + b k * ‖x‖ := add_le_add (d.past_error_le hb x k) (d.future_error_le hb x k)
    _ = _ := by ring

theorem norm_compression_sub_diagonal_le (hb : ∀ k, 0 ≤ b k)
    (C : ℝ) (hC : 0 ≤ C) (hbudget : ∀ k, b k * (1 + ‖T‖) ≤ C) :
    ‖(d.read.comp T).comp d.insert - d.diagonal‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg x))
  intro k
  exact (d.coordinate_error_le hb x k).trans
    (mul_le_mul_of_nonneg_right (hbudget k) (norm_nonneg x))

end MatrixAlmostDiagonalData
end ThesisCommon
