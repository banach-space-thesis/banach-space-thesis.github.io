import PFP.UncountableStatements
import ThesisCommon.Analysis.WCGEllOnePrimaryTransfer

/-! The full WCG ℓ1 clause of Theorem 4.1. The other standard-sum clauses
are separate assertions, so this declaration does not claim the conjunction. -/
noncomputable section
open scoped Cardinal
namespace PFP
open ThesisCommon
variable (𝕜 Γ X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem theorem_4_1_ellOne (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hX : IsWeaklyCompactlyGenerated 𝕜 X) :
    PrimarinessTransfer 𝕜 (EllOneSum ℕ X) (EllOneSum Γ X) Γ := by
  constructor
  · intro h
    have h' := hX.ellOne_isUniformlyPrimary_of_countable_model hΓ h
    exact ⟨h'.isPrimary, h'⟩
  · intro h hcof
    exact hX.ellOne_isPrimary_of_countable_model hΓ hcof h

end PFP
