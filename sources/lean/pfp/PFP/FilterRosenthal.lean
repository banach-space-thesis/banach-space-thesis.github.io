import PFP.FilterStatements
import ThesisCommon.Analysis.FilterRosenthal

/-! The original full-cardinality Rosenthal lemma (Lemma 6.8), for genuine
finitely additive real or complex measures with actual total variation.
No countable-additivity, regular-cardinal, or atomicity restriction is used. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u

/-- The full original manuscript statement of Lemma 6.8. -/
theorem lemma_6_8 (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u) [Infinite Γ] :
    Lemma_6_8 𝕜 Γ := by
  intro μ hμ hdiag η hη
  exact rosenthal_charge_selection μ hμ hdiag η hη

end PFP
