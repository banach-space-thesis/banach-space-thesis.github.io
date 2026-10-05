import ThesisCommon.Analysis.MatrixSumOperators

/-! Actual finite initial corners of bounded operators on scalar lp.
Insertion extends by zero and reading compresses to the same coordinates. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev ScalarLpOperator (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) :=
  lp (fun _ : ℕ => 𝕜) p.val →L[𝕜] lp (fun _ : ℕ => 𝕜) p.val

def finiteLpInitialEmbedding (n : ℕ) : Fin (n + 1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩

def finiteMatrixToLpOperator (p : BanachExponent) (n : ℕ) :
    FiniteMatrixBlock 𝕜 p (n + 1) →L[𝕜] ScalarLpOperator 𝕜 p :=
  operatorSandwich (lpExtend (𝕜 := 𝕜) (X := 𝕜) p.val (finiteLpInitialEmbedding n))
    (lpRestrict (𝕜 := 𝕜) (X := 𝕜) p.val (finiteLpInitialEmbedding n))

def lpOperatorToFiniteMatrix (p : BanachExponent) (n : ℕ) :
    ScalarLpOperator 𝕜 p →L[𝕜] FiniteMatrixBlock 𝕜 p (n + 1) :=
  operatorSandwich (lpRestrict (𝕜 := 𝕜) (X := 𝕜) p.val (finiteLpInitialEmbedding n))
    (lpExtend (𝕜 := 𝕜) (X := 𝕜) p.val (finiteLpInitialEmbedding n))

theorem norm_finiteMatrixToLpOperator_le (p : BanachExponent) (n : ℕ) :
    ‖finiteMatrixToLpOperator (𝕜 := 𝕜) p n‖ ≤ 1 := by
  apply (norm_operatorSandwich_le _ _).trans
  simpa only [mul_one] using mul_le_mul
    (norm_lpExtend_le (𝕜 := 𝕜) (X := 𝕜) (p := p.val) (finiteLpInitialEmbedding n))
    (norm_lpRestrict_le (𝕜 := 𝕜) (X := 𝕜) (p := p.val) (finiteLpInitialEmbedding n))
    (norm_nonneg _) zero_le_one

theorem norm_lpOperatorToFiniteMatrix_le (p : BanachExponent) (n : ℕ) :
    ‖lpOperatorToFiniteMatrix (𝕜 := 𝕜) p n‖ ≤ 1 := by
  apply (norm_operatorSandwich_le _ _).trans
  simpa only [mul_one] using mul_le_mul
    (norm_lpRestrict_le (𝕜 := 𝕜) (X := 𝕜) (p := p.val) (finiteLpInitialEmbedding n))
    (norm_lpExtend_le (𝕜 := 𝕜) (X := 𝕜) (p := p.val) (finiteLpInitialEmbedding n))
    (norm_nonneg _) zero_le_one

theorem lpOperatorToFiniteMatrix_comp_toLpOperator (p : BanachExponent) (n : ℕ) :
    (lpOperatorToFiniteMatrix (𝕜 := 𝕜) p n).comp (finiteMatrixToLpOperator p n) =
      ContinuousLinearMap.id 𝕜 (FiniteMatrixBlock 𝕜 p (n + 1)) := by
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro x
  change lpRestrict (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n)
      (lpExtend (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n)
        (A (lpRestrict (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n)
          (lpExtend (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n) x)))) = A x
  have h (y : FiniteLpSpace 𝕜 p (n + 1)) :
      lpRestrict (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n)
        (lpExtend (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n) y) = y :=
    DFunLike.congr_fun (lpRestrict_comp_extend (𝕜 := 𝕜) (X := 𝕜)
      (p := p.val) (finiteLpInitialEmbedding n)) y
  rw [h, h]

theorem finiteMatrixToLpOperator_apply_image (p : BanachExponent) (n : ℕ)
    (A : FiniteMatrixBlock 𝕜 p (n + 1)) (x : lp (fun _ : ℕ => 𝕜) p.val)
    (i : Fin (n + 1)) :
    finiteMatrixToLpOperator p n A x i.val = A (lpRestrict (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n) x) i :=
  lpExtend_apply_image (𝕜 := 𝕜) (p := p.val) _ _ _

theorem lpOperatorToFiniteMatrix_apply (p : BanachExponent) (n : ℕ)
    (A : ScalarLpOperator 𝕜 p) (x : FiniteLpSpace 𝕜 p (n + 1)) (i : Fin (n + 1)) :
    lpOperatorToFiniteMatrix p n A x i = A (lpExtend (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n) x) i.val := rfl

end ThesisCommon

