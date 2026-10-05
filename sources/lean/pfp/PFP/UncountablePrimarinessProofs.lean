import PFP.WCGEllOnePrimarinessProofs
import PFP.SeparableLpPrimarinessProofs
import PFP.SeparableCZeroPrimarinessProofs

/-! All clauses of the manuscript's uncountable primary transfer theorem,
assembled from actual WCG ell1 and separable lp/c0 constructions. -/
noncomputable section
namespace PFP
open ThesisCommon TopologicalSpace
variable (𝕜 Γ X : Type*) [RCLike 𝕜]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem theorem_4_1 : Theorem_4_1 𝕜 Γ X := by
  constructor
  · exact theorem_4_1_ellOne 𝕜 Γ X
  · intro hΓ hsep
    exact ⟨theorem_4_1_lp 𝕜 Γ X hΓ hsep, theorem_4_1_cZero 𝕜 Γ X hΓ hsep⟩

end PFP
