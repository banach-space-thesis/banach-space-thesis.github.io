import PFP.GeneralSumBlockStatements
import ThesisCommon.Analysis.WCGEllOneDiagonalSelection

/-! Exact Lemma 4.28 on the actual vector-valued ℓ₁ sum. -/
noncomputable section
namespace PFP
open ThesisCommon
variable (𝕜 Γ X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem lemma_4_28 : Lemma_4_28 𝕜 Γ X := by
  intro hΓ hX T
  exact hX.ellOne_diagonal_coordinates hΓ T

end PFP
