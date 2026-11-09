import CKEUPFP.CantorCZeroSelfSimilarity
import CKEUPFP.MilutinVector
import CKEUPFP.VendorDefinitions

/-! The genuine sequence self-similarity needed to deduce primariness.
The vector-valued Milutin equivalence transports the explicit Cantor
`c₀` decomposition to every uncountable compact metrizable domain. -/

noncomputable section

namespace CKEUPFP

variable {𝕜 : Type*} [RCLike 𝕜]
variable (K : Type*) [TopologicalSpace K] [TopologicalSpace.MetrizableSpace K]
  [CompactSpace K] [Uncountable K]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- An actual isomorphism with the countable null-sequence sum. -/
def continuousMapCZeroEquiv :
    C(K, E) ≃L[𝕜] ThesisCommon.CZeroSum C(K, E) :=
  (milutinVectorEquiv (𝕜 := 𝕜) K E).trans
    ((cantorCZeroEquiv (𝕜 := 𝕜) (E := E)).trans
      (ThesisCommon.cZeroMapEquiv (ι := ℕ) (milutinVectorEquiv (𝕜 := 𝕜) K E).symm))

/-- UPFP implies primariness here because sequence self-similarity has been
proved for these specific continuous-function spaces. -/
theorem continuousMap_isPrimary_of_hasUPFP (h : HasUPFP 𝕜 C(K, E)) :
    IsPrimary 𝕜 C(K, E) := by
  apply isPrimary_iff_vendor.mpr
  exact (hasUPFP_iff_vendor.mp h).isPrimary_of_sequenceSelfSimilar
    (Or.inr ⟨continuousMapCZeroEquiv (𝕜 := 𝕜) K E⟩)

end CKEUPFP
