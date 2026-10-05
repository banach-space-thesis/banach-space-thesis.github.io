import PFP.GeneralSumStatements
import PFP.WCGEllOneTransferProofs
import ThesisCommon.Analysis.UncountableSchauderTransfer

/-! Proofs of Theorem 4.3(ii),(iii) and the general symmetric-sum part of
Corollary 4.9. Both uniform and nonuniform clauses use the actual space and
bounded factors, and retain exactly the source's cardinal restrictions. -/
noncomputable section
namespace PFP
open ThesisCommon TopologicalSpace
variable (𝕜 Γ E X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem theorem_4_3_ii (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Theorem_4_3_ii 𝕜 Γ E X b := by
  intro hΓ hs hnot hsep
  letI : SeparableSpace X := hsep
  constructor
  · intro hX
    have h := UncountableSchauderSum.hasUPFP_of_separable hs hnot hΓ hX
    exact ⟨h.hasPFP, h⟩
  · intro hX hcof
    exact UncountableSchauderSum.hasPFP_of_separable hs hnot hΓ hcof hX

theorem theorem_4_3_iii (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Theorem_4_3_iii 𝕜 Γ E X b := by
  intro hΓ hs hnot htotal
  constructor
  · intro hX
    have h := UncountableSchauderSum.hasUPFP_of_countable_total_dual hs hnot htotal hΓ hX
    exact ⟨h.hasPFP, h⟩
  · intro hX hcof
    exact UncountableSchauderSum.hasPFP_of_countable_total_dual hs hnot htotal hΓ hcof hX

/-- All three alternatives of the source theorem, including the WCG ℓ₁
case proved separately and both general symmetric-sum cases above. -/
theorem theorem_4_3 (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Theorem_4_3 𝕜 Γ E X b :=
  ⟨theorem_4_3_i 𝕜 Γ X, theorem_4_3_ii 𝕜 Γ E X b, theorem_4_3_iii 𝕜 Γ E X b⟩

theorem corollary_4_9_general (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Corollary_4_9_general 𝕜 Γ E X b := by
  intro hΓ hs hnot hsep hX
  letI : SeparableSpace X := hsep
  exact UncountableSchauderSum.hasUPFP_of_separable hs hnot hΓ hX

end PFP
