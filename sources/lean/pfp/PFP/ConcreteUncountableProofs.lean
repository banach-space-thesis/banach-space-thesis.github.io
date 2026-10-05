import PFP.GeneralSumProofs
import ThesisCommon.Analysis.ConcreteUncountableTransfer

/-! Full Corollary 4.9, including its actual arbitrary-index ℓp and c₀
consequences, obtained through explicit coordinate-preserving isometries.
-/
noncomputable section
namespace PFP
open ThesisCommon TopologicalSpace
variable (𝕜 Γ X : Type*) [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [TopologicalSpace Γ] [DiscreteTopology Γ]

theorem corollary_4_9_concrete : Corollary_4_9_concrete 𝕜 Γ X := by
  intro hΓ hsep hX
  letI : SeparableSpace X := hsep
  constructor
  · intro p hp1 hp
    exact lp_hasUPFP_of_uncountable_separable hΓ p.val hp1 hp hX
  · exact cZero_hasUPFP_of_uncountable_separable hΓ hX

theorem corollary_4_9 (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] (b : NormalizedSchauderFamily 𝕜 Γ E) :
    Corollary_4_9 𝕜 Γ E X b :=
  ⟨corollary_4_9_general 𝕜 Γ E X b, corollary_4_9_concrete 𝕜 Γ X⟩

end PFP
