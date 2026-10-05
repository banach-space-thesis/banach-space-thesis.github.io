import ThesisCommon.Analysis.JamesSequenceSpaceComplete
import Mathlib.Analysis.Normed.Module.Dual

/-! Appendix B.4 on the actual James sequence spaces, with their finite-path
variation norm and proved Banach-space structure. These Prop targets do not
assume the structural ingredients used in the manuscript proof and are not
proofs of primariness. The James-tree convention issue PFP-S04 is unrelated.
-/
noncomputable section
namespace PFP
open ThesisCommon
open scoped ENNReal
variable (𝕜 : Type*) [RCLike 𝕜]

/-- Appendix B.4's conditional general-p assertion, exactly for 1<p<∞. -/
def Theorem_B_4_general (p : BanachExponent) : Prop :=
  1 < p.val → p.val ≠ ∞ →
    IsPrimary 𝕜 (JamesSequenceSpace 𝕜 p) →
      IsPrimary 𝕜 (StrongDual 𝕜 (JamesSequenceSpace 𝕜 p))

/-- Appendix B.4's unconditional conclusion for the classical James space. -/
def Theorem_B_4_classical : Prop :=
  IsPrimary 𝕜 (StrongDual 𝕜 (JamesSequenceSpace 𝕜 ⟨2, by norm_num⟩))

/-- Both clauses of Appendix B.4, `thm:Jp-dual-primary`. -/
def Theorem_B_4 : Prop :=
  (∀ p : BanachExponent, Theorem_B_4_general 𝕜 p) ∧ Theorem_B_4_classical 𝕜

end PFP
