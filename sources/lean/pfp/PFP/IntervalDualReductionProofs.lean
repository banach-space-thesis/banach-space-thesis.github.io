import PFP.MainStatements
import ThesisCommon.Analysis.IntervalDualPrimarinessReduction

/-! Corollary 4.7 reduced to the independent primariness theorem for
Lebesgue L1. The continuum representation and every other structural
premise are proved. This is a conditional reduction, not a completed
proof of the original corollary. -/
noncomputable section
namespace PFP
open ThesisCommon

theorem corollary_4_7_of_lebesgueL1_primary (𝕜 : Type*) [RCLike 𝕜]
    (hL1 : IsPrimary 𝕜 (IntervalLp 𝕜 ⟨1, le_rfl⟩)) : Corollary_4_7 𝕜 :=
  fun hCH => intervalContinuousDual_isPrimary_of_lebesgueL1_isPrimary 𝕜 hCH hL1

end PFP
