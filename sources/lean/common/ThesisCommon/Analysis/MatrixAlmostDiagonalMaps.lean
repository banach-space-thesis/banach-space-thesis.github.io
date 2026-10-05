import ThesisCommon.Analysis.MatrixAlmostDiagonalData
import ThesisCommon.Analysis.BoundedProductRetractions

/-! The contractive maps and actual diagonal operator associated to the
successive matrix blocks. All maps act on the full bounded product. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent}
variable {T : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p} {b : ℕ → ℝ}
namespace MatrixAlmostDiagonalData
variable (d : MatrixAlmostDiagonalData p T b)
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

def insert : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p :=
  boundedProductInsert d.n
    (fun k => matrixInsert p (d.row k).toEmbedding (d.col k).toEmbedding)
    (fun k => norm_matrixInsert_le p (d.row k).toEmbedding (d.col k).toEmbedding)

def read : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p :=
  boundedProductRead d.n
    (fun k => matrixRestrict p (d.row k).toEmbedding (d.col k).toEmbedding)
    (fun k => norm_matrixRestrict_le p (d.row k).toEmbedding (d.col k).toEmbedding)

theorem norm_insert_le : ‖d.insert‖ ≤ 1 := norm_boundedProductInsert_le _ _ _
theorem norm_read_le : ‖d.read‖ ≤ 1 := norm_boundedProductRead_le _ _ _

theorem insert_apply_image (x : FiniteMatrixSum 𝕜 p) (k : ℕ) :
    d.insert x (d.n k) = matrixInsert p (d.row k).toEmbedding (d.col k).toEmbedding (x k) :=
  boundedProductInsert_apply_image _ d.n_strictMono.injective _ _ _ _

theorem insert_apply_of_not_mem (x : FiniteMatrixSum 𝕜 p) (j : ℕ)
    (hj : j ∉ Set.range d.n) : d.insert x j = 0 :=
  boundedProductInsert_apply_of_not_mem _ _ _ _ _ hj

theorem read_apply (x : FiniteMatrixSum 𝕜 p) (k : ℕ) :
    d.read x k = matrixRestrict p (d.row k).toEmbedding (d.col k).toEmbedding (x (d.n k)) := rfl

theorem read_comp_insert : d.read.comp d.insert = ContinuousLinearMap.id 𝕜 _ :=
  boundedProductRead_comp_insert _ d.n_strictMono.injective _ _ _ _
    (fun k => matrixRestrict_comp_insert p (d.row k).toEmbedding (d.col k).toEmbedding)

theorem insert_single (k : ℕ) (x : FiniteMatrixBlock 𝕜 p (k + 1)) :
    d.insert (matrixSumSingle p k x) = matrixSumSingle p (d.n k)
      (matrixInsert p (d.row k).toEmbedding (d.col k).toEmbedding x) := by
  classical
  apply lp.ext
  funext j
  by_cases hj : j ∈ Set.range d.n
  · obtain ⟨i, rfl⟩ := hj
    rw [d.insert_apply_image]
    by_cases hi : i = k
    · subst i
      simp only [matrixSumSingle, lp.singleContinuousLinearMap_apply, lp.single_apply_self]
    · have hn : d.n i ≠ d.n k := fun h => hi (d.n_strictMono.injective h)
      simp only [matrixSumSingle, lp.singleContinuousLinearMap_apply, lp.single_apply_ne _ _ _ hi,
        lp.single_apply_ne _ _ _ hn, map_zero]
  · rw [d.insert_apply_of_not_mem _ _ hj]
    have hne : j ≠ d.n k := fun h => hj ⟨k, h.symm⟩
    simp only [matrixSumSingle, lp.singleContinuousLinearMap_apply, lp.single_apply_ne _ _ _ hne]

def diagonalEntry (k : ℕ) :
    FiniteMatrixBlock 𝕜 p (k + 1) →L[𝕜] FiniteMatrixBlock 𝕜 p (k + 1) :=
  (matrixSumCoordinate p k).comp ((d.read.comp T).comp (d.insert.comp (matrixSumSingle p k)))

theorem diagonalEntry_apply (k : ℕ) (x : FiniteMatrixBlock 𝕜 p (k + 1)) :
    d.diagonalEntry k x = matrixRestrict p (d.row k).toEmbedding (d.col k).toEmbedding
      (T (d.insert (matrixSumSingle p k x)) (d.n k)) := rfl

theorem norm_diagonalEntry_le (k : ℕ) : ‖d.diagonalEntry k‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  change ‖d.read (T (d.insert (matrixSumSingle p k x))) k‖ ≤ ‖T‖ * ‖x‖
  have hsingle : ‖matrixSumSingle (𝕜 := 𝕜) p k x‖ = ‖x‖ := lp.norm_single (by simp) _ _
  have hi : ‖d.insert (matrixSumSingle p k x)‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖d.insert‖ * ‖matrixSumSingle p k x‖ := d.insert.le_opNorm _
      _ ≤ 1 * ‖x‖ := mul_le_mul d.norm_insert_le hsingle.le (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  calc
    _ ≤ ‖d.read (T (d.insert (matrixSumSingle p k x)))‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero _ k
    _ ≤ ‖d.read‖ * ‖T (d.insert (matrixSumSingle p k x))‖ := d.read.le_opNorm _
    _ ≤ 1 * ‖T (d.insert (matrixSumSingle p k x))‖ :=
      mul_le_mul_of_nonneg_right d.norm_read_le (norm_nonneg _)
    _ = ‖T (d.insert (matrixSumSingle p k x))‖ := one_mul _
    _ ≤ ‖T‖ * ‖d.insert (matrixSumSingle p k x)‖ := T.le_opNorm _
    _ ≤ ‖T‖ * ‖x‖ := mul_le_mul_of_nonneg_left hi (norm_nonneg T)

def diagonal : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p :=
  boundedProductDiagonal d.diagonalEntry ‖T‖ (norm_nonneg T) d.norm_diagonalEntry_le

theorem diagonal_apply (x : FiniteMatrixSum 𝕜 p) (k : ℕ) :
    d.diagonal x k = d.diagonalEntry k (x k) := rfl

theorem isDiagonal : IsMatrixSumDiagonal p d.diagonal := ⟨d.diagonalEntry, fun _ _ => rfl⟩

theorem complement_compression :
    ContinuousLinearMap.id 𝕜 _ - (d.read.comp T).comp d.insert =
      (d.read.comp (ContinuousLinearMap.id 𝕜 _ - T)).comp d.insert := by
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_id, d.read_comp_insert]

end MatrixAlmostDiagonalData
end ThesisCommon
