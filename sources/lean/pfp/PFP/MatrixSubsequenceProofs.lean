import PFP.MatrixStatements
import ThesisCommon.Analysis.MatrixSubsequenceRange

noncomputable section
namespace PFP
open ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

theorem lemma_5_12 : Lemma_5_12 𝕜 := by
  intro p _ _ n hn hbound
  exact matrixSubsequenceCopy p n hn.injective hbound

end PFP
