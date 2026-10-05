import ThesisCommon.Analysis.MatrixOperatorSequences
import ThesisCommon.Analysis.LpOperatorBlocks

/-! The genuine bounded matrix product is a complemented subspace of
the operator space on scalar lp, realised on disjoint infinite blocks. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable (p : BanachExponent) (hp : 0 < p.val.toReal)
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

def matrixLpOperatorInsert : FiniteMatrixSum 𝕜 p →L[𝕜] ScalarLpOperator 𝕜 p :=
  (lpOperatorBlockInsert p hp).comp (matrixOperatorSequenceInsert p)

def matrixLpOperatorRead : ScalarLpOperator 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p :=
  (matrixOperatorSequenceRead p).comp (lpOperatorBlockRead p hp)

theorem norm_matrixLpOperatorInsert_le : ‖matrixLpOperatorInsert (𝕜 := 𝕜) p hp‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simpa only [mul_one] using mul_le_mul
    (norm_lpOperatorBlockInsert_le (𝕜 := 𝕜) p hp)
    (norm_matrixOperatorSequenceInsert_le (𝕜 := 𝕜) p)
    (norm_nonneg (matrixOperatorSequenceInsert (𝕜 := 𝕜) p)) zero_le_one

theorem norm_matrixLpOperatorRead_le : ‖matrixLpOperatorRead (𝕜 := 𝕜) p hp‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simpa only [mul_one] using mul_le_mul
    (norm_matrixOperatorSequenceRead_le (𝕜 := 𝕜) p)
    (norm_lpOperatorBlockRead_le (𝕜 := 𝕜) p hp)
    (norm_nonneg (lpOperatorBlockRead (𝕜 := 𝕜) p hp)) zero_le_one

theorem matrixLpOperatorRead_comp_insert :
    (matrixLpOperatorRead (𝕜 := 𝕜) p hp).comp (matrixLpOperatorInsert p hp) =
      ContinuousLinearMap.id 𝕜 (FiniteMatrixSum 𝕜 p) := by
  apply ContinuousLinearMap.ext
  intro x
  change matrixOperatorSequenceRead p
    (lpOperatorBlockRead p hp (lpOperatorBlockInsert p hp (matrixOperatorSequenceInsert p x))) = x
  have h := DFunLike.congr_fun (lpOperatorBlockRead_comp_insert p hp) (matrixOperatorSequenceInsert p x)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  rw [h]
  exact DFunLike.congr_fun (matrixOperatorSequenceRead_comp_insert p) x

end ThesisCommon
