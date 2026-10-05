import PFP.MatrixStatements
import ThesisCommon.Analysis.MatrixAlmostDiagonalSelection
import ThesisCommon.Analysis.MatrixAlmostDiagonalAssembly
import ThesisCommon.Analysis.MatrixGeometricControl

/-! Full Lemma 5.11. The source's geometric control is applied to the
actual inductive choice of matrix blocks and to all bounded product vectors. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem lemma_5_11 : Lemma_5_11 𝕜 := by
  intro p hp hfin T ε hε
  have hpReal : 1 < p.val.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hfin).mpr hp
  let b := matrixGeometricControl ε ‖T‖
  have hb (k : ℕ) : 0 < b k := matrixGeometricControl_pos hε (norm_nonneg T) k
  obtain ⟨d⟩ := exists_matrixAlmostDiagonalData p hpReal hfin T b hb
  refine ⟨d.read, d.insert, (d.read.comp T).comp d.insert, d.diagonal,
    d.norm_read_le, d.norm_insert_le, d.read_comp_insert, rfl, d.isDiagonal, ?_,
    d.complement_compression⟩
  have herror : ‖(d.read.comp T).comp d.insert - d.diagonal‖ ≤ ε / 16 :=
    d.norm_compression_sub_diagonal_le (fun k => (hb k).le)
      (ε / 16) (by positivity)
      (fun k => matrixGeometricControl_mul_le hε.le (norm_nonneg T) k)
  exact herror.trans_lt (by linarith)

end PFP
