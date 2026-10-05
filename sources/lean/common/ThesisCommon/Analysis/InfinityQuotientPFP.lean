import ThesisCommon.Analysis.InfinityQuotientCompression
import ThesisCommon.Analysis.InfinityQuotientScalarFactors

/-! The exact 2-PFP of the actual real or complex quotient ℓ∞/c₀.
The proof uses the established local scalar compression and genuine
contractive quotient reindex maps; no continuum hypothesis is used. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem infinityCZeroQuotient_hasCPFP_two :
    HasCPFP 𝕜 (InfinityCZeroQuotient 𝕜) 2 := by
  intro T
  obtain ⟨B, hB, _, c, hc⟩ :=
    exists_infinityQuotient_scalar_compression T Set.infinite_univ
  exact infinityQuotient_factor_dichotomy_of_mask_compression T B c hB hc

end ThesisCommon
