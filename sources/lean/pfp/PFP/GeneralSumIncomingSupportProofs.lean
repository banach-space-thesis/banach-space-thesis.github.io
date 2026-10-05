import PFP.GeneralSumStatements
import ThesisCommon.Analysis.UncountableSchauderIncomingSupport

/-! Full incoming-coordinate results 4.17 and 4.18. The finite lower-estimate
argument supplies the scalar support theorem; the countable total dual set
then supplies the operator theorem. No additional operator hypotheses occur. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u v w
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u)
  (E : Type v) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (X : Type w) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem lemma_4_17 (b : NormalizedSchauderFamily 𝕜 Γ E) : Lemma_4_17 𝕜 Γ E X b := by
  intro hs hnot φ T
  exact UncountableSchauderSum.functional_countable_coordinate_support hs hnot (φ.comp T)

theorem lemma_4_18 (b : NormalizedSchauderFamily 𝕜 Γ E) : Lemma_4_18 𝕜 Γ E X b := by
  intro hs hnot htotal T
  exact UncountableSchauderSum.operator_countable_incoming_support hs hnot htotal T

end PFP
