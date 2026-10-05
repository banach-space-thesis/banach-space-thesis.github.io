import PFP.IntervalDualReductionProofs
import ThesisCommon.Analysis.IntervalDualPrimarinessFinal

/-! Exact Corollary 4.7 (`cor:intro-C01`). The actual Lebesgue L1 input is
proved for real and complex scalars; the only hypothesis is the printed
negation of CH, expressed by the strict continuum cardinal inequality. -/
noncomputable section
namespace PFP
open ThesisCommon

theorem corollary_4_7 (𝕜 : Type*) [RCLike 𝕜] : Corollary_4_7 𝕜 :=
  intervalContinuousDual_isPrimary 𝕜

end PFP
