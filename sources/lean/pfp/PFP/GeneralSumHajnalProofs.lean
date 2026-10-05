import PFP.GeneralSumBlockStatements
import ThesisCommon.Analysis.UncountableSchauderHajnalSelection

/-! Full Lemma 4.29 and context-restored Lemma 4.27. The unrestricted
printed 4.27 formula is not asserted for countable coordinate sets. -/
noncomputable section
namespace PFP
open ThesisCommon
variable (𝕜 Γ E X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem lemma_4_27_uncountable (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Lemma_4_27 𝕜 Γ X E b := by
  intro hΓ hs T hsupport
  rcases hsupport with ⟨hlarge, hlocal⟩ | hboth
  · exact UncountableSchauderSum.diagonal_coordinates_of_locally_countable_either
      hlarge T hlocal
  · exact UncountableSchauderSum.diagonal_coordinates_of_two_sided_countable
      hΓ T (fun γ => (hboth γ).1) (fun γ => (hboth γ).2)

theorem lemma_4_29 (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Lemma_4_29 𝕜 Γ X E b := by
  intro hΓ hs hnot htotal T
  exact UncountableSchauderSum.diagonal_coordinates_of_countable_total_dual
    hs hnot htotal hΓ T

end PFP
