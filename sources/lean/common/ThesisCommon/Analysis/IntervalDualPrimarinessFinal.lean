import ThesisCommon.Analysis.AtomlessL1PrimaryFactorization
import ThesisCommon.Analysis.IntervalDualPrimarinessReduction

/-! Unconditional analytic input for the manuscript's anti-CH corollary:
the actual Lebesgue L1 primariness theorem discharges the last premise of
the already established continuum-sum representation argument. -/
noncomputable section
namespace ThesisCommon

theorem intervalContinuousDual_isPrimary (𝕜 : Type*) [RCLike 𝕜]
    (hCH : (Cardinal.aleph 1 : Cardinal.{0}) < Cardinal.continuum) :
    IsPrimary 𝕜 (IntervalContinuous 𝕜 →L[𝕜] 𝕜) :=
  intervalContinuousDual_isPrimary_of_lebesgueL1_isPrimary 𝕜 hCH (intervalL1_isPrimary 𝕜)

end ThesisCommon
