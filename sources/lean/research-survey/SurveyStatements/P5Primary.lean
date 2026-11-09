import SurveyStatements.P5SelfSimilarity
import SurveyStatements.P5Support.PelczynskiDecomposition

/-! The actual self-similarity of the mixed Bochner space supplies the
Pełczyński premise. Thus its uniform primary factorization implies precisely
the source's separate primariness assertion. It does not assume factorization
has already been proved. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal

namespace SurveyStatements.P5

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem mixedNorm_primary_of_uniformPrimaryFactorization (hp : p ≠ ∞)
    (h : HasUniformPrimaryFactorization 𝕜 (MixedNorm 𝕜 p)) :
    IsPrimary 𝕜 (MixedNorm 𝕜 p) := by
  have hPFP : P5Support.HasPFP 𝕜 (MixedNorm 𝕜 p) := by
    obtain ⟨K, _, hK⟩ := h
    intro T
    obtain ⟨A, B, _, heq⟩ := hK T
    rcases heq with heq | heq
    · exact Or.inl ⟨A, B, heq⟩
    · exact Or.inr ⟨A, B, heq⟩
  have hSelf : P5Support.IsSequenceSelfSimilar 𝕜 (MixedNorm 𝕜 p) :=
    Or.inl ⟨⟨p, Fact.out⟩, ⟨(mixedNormSelfSimilarity 𝕜 p hp).toContinuousLinearEquiv⟩⟩
  exact P5Support.HasPFP.isPrimary_of_sequenceSelfSimilar hPFP hSelf

end SurveyStatements.P5
