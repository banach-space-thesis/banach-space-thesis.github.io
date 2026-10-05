import PFP.UncountableStatements
import ThesisCommon.Analysis.WCGEllOneFactorizationTransfer

/-! Full Theorem 4.3(i), including both the uniform and plain-PFP alternatives. -/
noncomputable section
namespace PFP
open ThesisCommon

theorem theorem_4_3_i (𝕜 Γ X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] :
    Theorem_4_3_i 𝕜 Γ X := by
  intro hΓ hX
  constructor
  · intro hPFP
    have h := hX.ellOne_hasUPFP hΓ hPFP
    exact ⟨h.hasPFP, h⟩
  · intro hPFP hcof
    exact hX.ellOne_hasPFP_of_uncountable_cofinality hΓ hcof hPFP

end PFP
