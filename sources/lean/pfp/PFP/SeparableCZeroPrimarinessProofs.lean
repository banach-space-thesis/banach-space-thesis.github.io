import PFP.UncountableStatements
import ThesisCommon.Analysis.SeparableCZeroPrimaryTransfer

/-! The full c₀ clause of Theorem 4.1(ii), including both the uniform
alternative and the nonuniform alternative with uncountable cofinality. -/
noncomputable section
open scoped Cardinal ZeroAtInfty
namespace PFP
open ThesisCommon TopologicalSpace
variable (𝕜 Γ X : Type*) [RCLike 𝕜]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem theorem_4_1_cZero (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (hsep : SeparableSpace X) :
    PrimarinessTransfer 𝕜 (CZeroSum X) C₀(Γ, X) Γ := by
  letI := hsep
  constructor
  · intro h
    have h' := cZero_isUniformlyPrimary_of_countable_model hΓ h
    exact ⟨h'.isPrimary, h'⟩
  · intro h hcof
    exact cZero_isPrimary_of_countable_model hΓ hcof h

end PFP
