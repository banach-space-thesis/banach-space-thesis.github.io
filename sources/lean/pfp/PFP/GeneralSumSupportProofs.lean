import PFP.GeneralSumStatements
import ThesisCommon.Analysis.UncountableSchauderCountableSupport

/-! Full Lemmas 4.12 and 4.13 on the manuscript's actual arbitrary-index
symmetric sums. The two results retain the exact public statement targets.
-/
noncomputable section
namespace PFP
open ThesisCommon

variable (𝕜 Γ E X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Lemma 4.12, `lem:countable-support-lp-c0`, for the full E(Γ,X) space. -/
theorem lemma_4_12 (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Lemma_4_12 𝕜 Γ E X b := by
  intro hs x
  exact UncountableSchauderSum.countable_support x

/-- Lemma 4.13, `lem:separable-support-lp-c0`, for every norm-separable subset. -/
theorem lemma_4_13 (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Lemma_4_13 𝕜 Γ E X b := by
  intro hs s hsep
  exact UncountableSchauderSum.separable_countable_support hsep

end PFP
