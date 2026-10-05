import PFP.GeneralSumBlockStatements
import ThesisCommon.Analysis.UncountableSchauderDiagonalSelection

/-! Context-restored 4.30. The unrestricted `_asPrinted` formula is
deliberately not asserted: PFP-S05 records its missing cardinal premise. -/
noncomputable section
namespace PFP
open ThesisCommon
variable (𝕜 Γ E X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem lemma_4_30_uncountable (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Lemma_4_30 𝕜 Γ X E b := by
  intro hΓ hs hnot hsep T
  letI := hsep
  exact UncountableSchauderSum.diagonal_coordinates_of_separable hs hnot hΓ T

end PFP
