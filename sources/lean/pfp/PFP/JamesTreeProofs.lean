import PFP.JamesTreeStatements
import ThesisCommon.Analysis.JamesTreeUniformFactorization

/-! The two unchanged formulations of Theorem 5.4, each proved on its actual
completed space. The uniform factor bound is twelve, for every finite p>1
and every RCLike scalar field. No equivalence between the norms is asserted. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

theorem theorem_5_4_asPrinted : Theorem_5_4_asPrinted 𝕜 := by
  intro p hp hpinf
  apply literalJamesTree_hasUPFP
  have h := (ENNReal.toReal_lt_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞) hpinf).2 hp
  simpa only [ENNReal.toReal_one] using h

theorem theorem_5_4_consecutive : Theorem_5_4_consecutive 𝕜 := by
  intro p hp hpinf
  apply consecutiveJamesTree_hasUPFP
  have h := (ENNReal.toReal_lt_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞) hpinf).2 hp
  simpa only [ENNReal.toReal_one] using h

/-- The original theorem uses the manuscript's explicit finite-chain norm. -/
theorem theorem_5_4 : Theorem_5_4_asPrinted 𝕜 := theorem_5_4_asPrinted 𝕜

end PFP
