import ThesisCommon.Analysis.JamesTreeSpace
import ThesisCommon.Analysis.Primary

/-! The two explicit readings of Theorem 5.4 on their actual completed tree
spaces. The targets are proved in PFP.JamesTreeProofs, separately for each norm.
The manuscript defines a segment to be a finite chain; the cited classical
model instead requires consecutive nodes. Both readings are preserved without
choosing an unqualified JT_p alias or identifying the two norms.
-/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

/-- Theorem 5.4 with the manuscript's literal finite-chain definition. -/
def Theorem_5_4_asPrinted : Prop :=
  ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
    HasUPFP 𝕜 (LiteralChainJamesTreeSpace 𝕜 p)

/-- The separately labelled consecutive-segment formulation. No equivalence
with the printed target is assumed. -/
def Theorem_5_4_consecutive : Prop :=
  ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
    HasUPFP 𝕜 (ConsecutiveJamesTreeSpace 𝕜 p)

end PFP
