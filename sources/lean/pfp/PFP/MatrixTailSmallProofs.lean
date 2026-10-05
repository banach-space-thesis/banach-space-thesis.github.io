import PFP.MatrixStatements
import ThesisCommon.Analysis.BoundedProductFiniteTarget

/-! Full Lemma 5.10 on the actual bounded product of matrix blocks. -/
noncomputable section
namespace PFP
open ThesisCommon

theorem lemma_5_10 (𝕜 F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] :
    Lemma_5_10 𝕜 F := by
  intro p _hp1 _hp S J hJ η hη
  obtain ⟨I, hIJ, hI, hsmall⟩ := boundedProductMask_finite_target_small S J hJ hη
  have hmask : boundedProductMask (𝕜 := 𝕜)
      (E := fun n => FiniteMatrixBlock 𝕜 p (n + 1)) I = matrixSumMask p I := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext n
    simp only [boundedProductMask_apply, matrixSumMask_apply]
  exact ⟨I, hIJ, hI, by simpa only [hmask] using hsmall⟩

end PFP
