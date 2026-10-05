import ThesisCommon.Analysis.MatrixHilbertSchmidtBounds
import ThesisCommon.Analysis.MatrixSumOperators
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual finite matrix operator spaces are finite-dimensional through
their injective array of scalar entries. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem finiteMatrixBlock_finiteDimensional (p : BanachExponent) (N : ℕ) :
    FiniteDimensional 𝕜 (FiniteMatrixBlock 𝕜 p N) := by
  let T : FiniteMatrixBlock 𝕜 p N →ₗ[𝕜] (Fin N × Fin N → 𝕜) :=
    { toFun := fun A ij => matrixEntry p ij.1 ij.2 A
      map_add' := by intro A B; funext ij; exact map_add _ _ _
      map_smul' := by intro c A; funext ij; exact map_smul _ _ _ }
  apply FiniteDimensional.of_injective T
  intro A B h
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  rw [finiteMatrix_apply_eq_sum, finiteMatrix_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun c => x j * c) (congrFun h (i, j))

end ThesisCommon
