import Posets.MatrixIdealTransportAlgebra
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Genuine bounded operators on a finite power as matrices of bounded operators. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
open ThesisCommon
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {ι : Type*} [Fintype ι]

def operatorBlockMatrix (T : (ι → E) →L[𝕜] (ι → E)) : Matrix ι ι (E →L[𝕜] E) :=
  fun i j => (ContinuousLinearMap.proj i).comp
    (T.comp (ContinuousLinearMap.single 𝕜 (fun _ : ι => E) j))

@[simp] theorem operatorBlockMatrix_apply (T : (ι → E) →L[𝕜] (ι → E)) (i j : ι) (x : E) :
    operatorBlockMatrix T i j x = T (Pi.single j x) i := rfl

def operatorOfBlockMatrix (M : Matrix ι ι (E →L[𝕜] E)) : (ι → E) →L[𝕜] (ι → E) :=
  ContinuousLinearMap.pi (fun i => ∑ j, (M i j).comp (ContinuousLinearMap.proj j))

@[simp] theorem operatorOfBlockMatrix_apply (M : Matrix ι ι (E →L[𝕜] E)) (x : ι → E) (i : ι) :
    operatorOfBlockMatrix M x i = ∑ j, M i j (x j) := by
  simp [operatorOfBlockMatrix, ContinuousLinearMap.pi_apply]

theorem operatorOfBlockMatrix_blockMatrix (T : (ι → E) →L[𝕜] (ι → E)) :
    operatorOfBlockMatrix (operatorBlockMatrix T) = T := by
  ext x i
  have h := congrFun (ContinuousLinearMap.sum_comp_single 𝕜 (fun _ : ι => E) T x) i
  simpa [operatorOfBlockMatrix_apply, operatorBlockMatrix_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, Finset.sum_apply] using h

theorem blockMatrix_operatorOfBlockMatrix (M : Matrix ι ι (E →L[𝕜] E)) :
    operatorBlockMatrix (operatorOfBlockMatrix M) = M := by
  ext i j x
  simp [operatorBlockMatrix_apply, operatorOfBlockMatrix_apply, Pi.single_apply, apply_ite]

theorem operatorBlockMatrix_mul (T S : (ι → E) →L[𝕜] (ι → E)) :
    operatorBlockMatrix (T*S) = operatorBlockMatrix T * operatorBlockMatrix S := by
  ext i j x
  have h := congrFun (ContinuousLinearMap.sum_comp_single 𝕜 (fun _ : ι => E) T (S (Pi.single j x))) i
  simpa [operatorBlockMatrix, Matrix.mul_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, Finset.sum_apply] using h.symm

/-- This is a ring equivalence between actual bounded-operator algebras. -/
def operatorBlockMatrixRingEquiv :
    ((ι → E) →L[𝕜] (ι → E)) ≃+* Matrix ι ι (E →L[𝕜] E) where
  toFun := operatorBlockMatrix
  invFun := operatorOfBlockMatrix
  left_inv := operatorOfBlockMatrix_blockMatrix
  right_inv := blockMatrix_operatorOfBlockMatrix
  map_add' := by intro T S; ext i j x; rfl
  map_mul' := operatorBlockMatrix_mul

open scoped Matrix.Norms.Operator

set_option synthInstance.maxSize 4096 in
/-- Any finite nonempty power has a unique maximal closed operator ideal
exactly when the original Banach space does. -/
theorem uniqueMaximalClosed_finitePower_iff [CompleteSpace E] [Nonempty ι] :
    HasUniqueMaximalClosedIdeal 𝕜 ((ι → E) →L[𝕜] (ι → E)) ↔
      HasUniqueMaximalClosedIdeal 𝕜 (E →L[𝕜] E) := by
  letI : CompleteSpace (Matrix ι ι (E →L[𝕜] E)) :=
    inferInstanceAs (CompleteSpace (ι → PiLp 1 (fun _ : ι => E →L[𝕜] E)))
  exact (uniqueMaximalClosed_ringEquiv (𝕜 := 𝕜) (operatorBlockMatrixRingEquiv (ι := ι))).trans
    (uniqueMaximalClosed_matrix_equiv (𝕜 := 𝕜) (A := E →L[𝕜] E) ι).symm

end Posets



