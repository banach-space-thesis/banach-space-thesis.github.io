import PFP.MainStatements
import ThesisCommon.Analysis.FiniteOrdinalCoefficients

/-! The finite-ordinal cases of Corollary 4.10. These prove the exact original
conclusions for α < ω; they do not claim either unrestricted clause complete.
The coefficient spaces are absorbed by genuine bounded sum isomorphisms. -/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace PFP
open ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u) (α : Ordinal.{v})

theorem corollary_4_10_i_of_finite (hα : α < Ordinal.omega0) :
    Corollary_4_10_i 𝕜 Γ α := by
  letI := ordinalContinuous_nontrivial 𝕜 α
  letI := ordinalContinuous_finiteDimensional 𝕜 hα
  intro hΓ p hp
  exact ⟨finiteCoefficient_lp_hasUPFP_of_large_index hΓ p.val hp,
    finiteCoefficient_lp_primary_of_large_index hΓ p.val hp⟩

theorem corollary_4_10_ii_of_finite [TopologicalSpace Γ] [DiscreteTopology Γ]
    (hα : α < Ordinal.omega0) : Corollary_4_10_ii 𝕜 Γ α := by
  letI := ordinalContinuous_nontrivial 𝕜 α
  letI := ordinalContinuous_finiteDimensional 𝕜 hα
  intro _ hΓ
  exact ⟨fun p hp1 hp => finiteCoefficient_lp_hasUPFP hΓ p.val hp1 hp,
    finiteCoefficient_cZero_hasUPFP hΓ⟩

end PFP
