import ThesisCommon.Analysis.JamesFiniteSectionAbsorption

/-! Every increasing James interval decomposition starting at zero is
uniformly equivalent to its actual finite initial-section sum. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
  (σ : ℕ → ℕ) (hσ : StrictMono σ) (hzero : σ 0 = 0)

def jamesBlockLengths (n : ℕ) : ℕ := σ (n + 1) - σ n - 1

include hσ hzero in
theorem jamesBlockEndpoints_lengths : jamesBlockEndpoints (jamesBlockLengths σ) = σ := by
  funext n
  induction n with
  | zero => exact hzero.symm
  | succ n ih =>
    rw [jamesBlockEndpoints_succ, ih]
    have hs : σ n < σ (n + 1) := hσ (Nat.lt_succ_self n)
    change σ n + 1 + (σ (n + 1) - σ n - 1) = σ (n + 1)
    omega

def jamesBlockFiniteSectionEquiv :
    JamesBlockSum (𝕜 := 𝕜) p σ ≃L[𝕜]
      JamesFiniteSectionSum (𝕜 := 𝕜) p (jamesBlockLengths σ) := by
  have e := (jamesFiniteSectionSumEquivBlocks (𝕜 := 𝕜) p hp (jamesBlockLengths σ)).symm
  rw [jamesBlockEndpoints_lengths σ hσ hzero] at e
  exact e

end ThesisCommon
