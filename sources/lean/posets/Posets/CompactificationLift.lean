import Posets.CompactificationLiftCorner

noncomputable section
open scoped ZeroAtInfty OnePoint
namespace Posets

variable (𝕜 : Type) [RCLike 𝕜]

/-- Lemma 8.3: compression along the one-point compactification lifts any
algebra homomorphism that annihilates finite-rank operators, and preserves
its range, continuity and compactness in both directions. -/
theorem lemma_8_3_proof (K₀ : Type) [TopologicalSpace K₀]
    [LocallyCompactSpace K₀] [T2Space K₀]
    (C : Type) [NormedRing C] [NormedAlgebra 𝕜 C] [CompleteSpace C]
    (Ψ : (C₀(K₀, 𝕜) →L[𝕜] C₀(K₀, 𝕜)) →ₗ[𝕜] C) :
    Lemma_8_3 𝕜 K₀ C Ψ := by
  intro hmul hfin
  exact corner_homomorphism_lift (compactificationInclusion K₀)
    (compactificationProjection K₀) (compactificationProjection_inclusion K₀)
    (ContinuousMap.evalCLM 𝕜 ∞) 1 (compactification_decomposition K₀) Ψ hmul hfin

end Posets
