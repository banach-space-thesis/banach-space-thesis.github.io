import ThesisCommon.Analysis.LpOperatorFiniteCorners
import ThesisCommon.Analysis.BoundedProductRetractions

/-! Coordinatewise initial-corner insertion into the bounded product of
lp operator spaces, with its actual contractive readback. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable (p : BanachExponent)
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

def matrixOperatorSequenceInsert :
    FiniteMatrixSum 𝕜 p →L[𝕜] lp (fun _ : ℕ => ScalarLpOperator 𝕜 p) ∞ :=
  boundedProductDiagonal (fun n => finiteMatrixToLpOperator p n) 1 zero_le_one
    (fun n => norm_finiteMatrixToLpOperator_le p n)

def matrixOperatorSequenceRead :
    lp (fun _ : ℕ => ScalarLpOperator 𝕜 p) ∞ →L[𝕜] FiniteMatrixSum 𝕜 p :=
  boundedProductDiagonal (fun n => lpOperatorToFiniteMatrix p n) 1 zero_le_one
    (fun n => norm_lpOperatorToFiniteMatrix_le p n)

theorem matrixOperatorSequenceInsert_apply (x : FiniteMatrixSum 𝕜 p) (n : ℕ) :
    matrixOperatorSequenceInsert p x n = finiteMatrixToLpOperator p n (x n) := rfl

theorem matrixOperatorSequenceRead_apply
    (x : lp (fun _ : ℕ => ScalarLpOperator 𝕜 p) ∞) (n : ℕ) :
    matrixOperatorSequenceRead p x n = lpOperatorToFiniteMatrix p n (x n) := rfl

theorem norm_matrixOperatorSequenceInsert_le : ‖matrixOperatorSequenceInsert (𝕜 := 𝕜) p‖ ≤ 1 :=
  norm_boundedProductDiagonal_le _ _ _ _

theorem norm_matrixOperatorSequenceRead_le : ‖matrixOperatorSequenceRead (𝕜 := 𝕜) p‖ ≤ 1 :=
  norm_boundedProductDiagonal_le _ _ _ _

theorem matrixOperatorSequenceRead_comp_insert :
    (matrixOperatorSequenceRead (𝕜 := 𝕜) p).comp (matrixOperatorSequenceInsert p) =
      ContinuousLinearMap.id 𝕜 (FiniteMatrixSum 𝕜 p) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  exact DFunLike.congr_fun (lpOperatorToFiniteMatrix_comp_toLpOperator p n) (x n)

end ThesisCommon
