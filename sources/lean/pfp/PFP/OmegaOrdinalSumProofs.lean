import PFP.MainStatements
import ThesisCommon.Analysis.OmegaOrdinalCoefficient

/-! The first infinite ordinal cases of Corollary 4.10, using a constructed
C([0,ω]) ≃ c₀ equivalence. Arbitrary countable ordinals remain a separate
quantitative preservation problem. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u)

theorem corollary_4_10_i_omega : Corollary_4_10_i 𝕜 Γ Ordinal.omega0.{v} := by
  intro hΓ p hp
  exact ⟨omegaOrdinal_lp_hasUPFP_of_large_index hΓ p.val hp,
    omegaOrdinal_lp_primary_of_large_index hΓ p.val hp⟩

theorem corollary_4_10_ii_omega [TopologicalSpace Γ] [DiscreteTopology Γ] :
    Corollary_4_10_ii 𝕜 Γ Ordinal.omega0.{v} := by
  letI := omegaOrdinal_separable 𝕜
  intro _ hΓ
  exact ⟨fun p hp1 hp => lp_hasUPFP_of_uncountable_separable hΓ p.val hp1 hp
      (omegaOrdinal_hasUPFP 𝕜),
    cZero_hasUPFP_of_uncountable_separable hΓ (omegaOrdinal_hasUPFP 𝕜)⟩

end PFP
