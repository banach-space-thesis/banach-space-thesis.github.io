import PFP.SymmetricBasis
import ThesisCommon.Analysis.UnconditionalWeakNullIff

/-! Full Lemma 3.1 on an arbitrary normalized unconditional Schauder basis,
with the actual closed-span isomorphism target and arbitrary RCLike scalars. -/
noncomputable section
namespace PFP
open ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

theorem lemma_3_1 (b : NormalizedSchauderBasis 𝕜 X) : Lemma_3_1 b :=
  b.no_ellOne_subsequence_iff_rows_tendsto_zero

end PFP
