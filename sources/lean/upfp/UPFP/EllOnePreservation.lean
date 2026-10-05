import UPFP.MainStatements
import ThesisCommon.Analysis.EllOneSelfSimilarPreservation
import ThesisCommon.Analysis.SequencePrimariness

/-! The entire self-similarity branch of Theorem 1.1. The separate
finite-cotype hypothesis on the dual is not assumed or discharged here. -/
namespace UPFP
open ThesisCommon

alias proposition_5_2_lp := ThesisCommon.ellOne_lp_diagonal_reduction
alias proposition_5_2_cZero := ThesisCommon.ellOne_cZero_diagonal_reduction

/-- Both conclusions of Theorem 1.1 for any of its self-similarity cases:
all p in [1,infinity], or c0. This is a proved branch of the original target. -/
theorem theorem_1_1_selfSimilar {𝕜 : Type*} [RCLike 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (hX : HasUPFP 𝕜 X) (hself : IsSequenceSelfSimilar 𝕜 X) :
    HasUPFP 𝕜 (EllOneSum ℕ X) ∧ IsPrimary 𝕜 (EllOneSum ℕ X) := by
  have h := hX.ellOne_of_sequenceSelfSimilar hself
  exact ⟨h, h.lp_isPrimary⟩

end UPFP
