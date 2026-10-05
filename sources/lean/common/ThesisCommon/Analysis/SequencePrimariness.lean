import ThesisCommon.Analysis.PelczynskiDecomposition
import ThesisCommon.Analysis.InfinitySelfSimilarity
import ThesisCommon.Analysis.CZeroSelfSimilarity
import ThesisCommon.Analysis.LpSelfSimilarity

/-! Primariness from primary factorisation on actual countable sequence sums.
Self-similarity is supplied by the checked pairing isomorphisms, and the
range identification by the checked Pełczyński decomposition argument.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem HasPFP.lp_isPrimary {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (h : HasPFP 𝕜 (lp (fun _ : ℕ => X) p)) : IsPrimary 𝕜 (lp (fun _ : ℕ => X) p) :=
  h.isPrimary_of_sequenceSelfSimilar (lp_sequenceSelfSimilar p)

theorem HasUPFP.lp_isPrimary {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (h : HasUPFP 𝕜 (lp (fun _ : ℕ => X) p)) : IsPrimary 𝕜 (lp (fun _ : ℕ => X) p) :=
  h.hasPFP.lp_isPrimary

theorem HasPFP.infinity_isPrimary (h : HasPFP 𝕜 (EllInfinitySum X)) :
    IsPrimary 𝕜 (EllInfinitySum X) :=
  h.isPrimary_of_sequenceSelfSimilar infinity_sequenceSelfSimilar

theorem HasPFP.cZero_isPrimary (h : HasPFP 𝕜 (CZeroSum X)) :
    IsPrimary 𝕜 (CZeroSum X) :=
  h.isPrimary_of_sequenceSelfSimilar cZero_sequenceSelfSimilar

theorem HasUPFP.infinity_isPrimary (h : HasUPFP 𝕜 (EllInfinitySum X)) :
    IsPrimary 𝕜 (EllInfinitySum X) := h.hasPFP.infinity_isPrimary

theorem HasUPFP.cZero_isPrimary (h : HasUPFP 𝕜 (CZeroSum X)) :
    IsPrimary 𝕜 (CZeroSum X) := h.hasPFP.cZero_isPrimary

end ThesisCommon
